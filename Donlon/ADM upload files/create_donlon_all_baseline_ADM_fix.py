#!/usr/bin/env python3
"""
====================================================================
Donlon ALL Baseline - ADM upload
Created by: Paul-Adrian LAPUSAN (for EUROCONTROL)
====================================================================
Reads a Donlon AIXM 5.1.1 BasicMessage file, copies every feature verbatim and applies a set of user-selectable corrections, writing the result to a new file.
The original XML declaration, leading comments and the root element layout are preserved byte-for-byte; only the touched elements change.

Corrections
-----------
1. translate-limits (GND / UNL / FLOOR / CEILING):
   - <aixm:upperLimit>UNL</aixm:upperLimit> -> <aixm:upperLimit uom="FL">999</aixm:upperLimit>
   - <aixm:lowerLimit>GND</aixm:lowerLimit> -> <aixm:lowerLimit uom="M">0</aixm:lowerLimit>, or uom="FT" when the
        sibling upperLimit is expressed in FT or FL (UNL is translated first, so an UNL sibling counts as FL -> FT).
   - Airspace: <aixm:lowerLimit>FLOOR</aixm:lowerLimit> / <aixm:upperLimit>CEILING</aixm:upperLimit> inside an aixm:AirspaceLayer are
        replaced with the actual value+uom taken from the airspace's aixm:geometryComponent/aixm:theAirspaceVolume limits.  When the airspace has
        several volumes / parts, FLOOR takes the lowest lowerLimit and CEILING the highest upperLimit (compared in feet).
   - RouteSegment: FLOOR / CEILING inside an aixm:AirspaceLayer are replaced with the value+uom of the aixm:lowerLimit / aixm:upperLimit foundd
        directly under the aixm:RouteSegmentTimeSlice.

2. fix-timesheets:
   - every aixm:timeInterval/aixm:Timesheet that is not nil but has no aixm:startDate and aixm:endDate gets, immediately after aixm:timeReference:
       <aixm:startDate>01-01</aixm:startDate>
       <aixm:endDate>31-12</aixm:endDate>

Omitted features
----------------
The following are dropped entirely from the output:
   - the StandardLevelColumn / StandardLevelTable / StandardLevelSector features (by type, IGNORED_FEATURE_TYPES);
   - a fixed set of features by gml:identifier UUID (IGNORED_FEATURE_UUIDS): the FIR / UIR airspaces, the STATE and DONLON CIVIL AVIATION ADMINISTRATION
     OrganisationAuthorities, the NOF Unit and the GeoBorder.
References from kept features to any omitted feature are left pointing at the original UUIDs (i.e. become dangling); they are not re-targeted or niled.

Usage:
  python create_donlon_all_baseline_ADM_fix.py --input Donlon_ALL_Baseline.xml
  python create_donlon_all_baseline_ADM_fix.py --input in.xml --output out.xml
  python create_donlon_all_baseline_ADM_fix.py --input in.xml --translate-limits yes --fix-timesheets no
"""

import argparse
import os
import re
import sys
from lxml import etree

AIXM = '{http://www.aixm.aero/schema/5.1.1}'
MSG = '{http://www.aixm.aero/schema/5.1.1/message}'
XSI_NIL = '{http://www.w3.org/2001/XMLSchema-instance}nil'
XLINK_HREF = '{http://www.w3.org/1999/xlink}href'
GML_IDENTIFIER = '{http://www.opengis.net/gml/3.2}identifier'

UPPER = AIXM + 'upperLimit'
LOWER = AIXM + 'lowerLimit'
TIMESHEET = AIXM + 'Timesheet'
TIME_INTERVAL = AIXM + 'timeInterval'
TIME_REFERENCE = AIXM + 'timeReference'
START_DATE = AIXM + 'startDate'
END_DATE = AIXM + 'endDate'

# Opening tag of the message root, used to splice the original (verbatim) header
# onto the lxml-serialised body so the declaration, leading comments and root
# attribute layout are preserved exactly.
_ROOT_RE = re.compile(r'<message:AIXMBasicMessage\b[^>]*>', re.DOTALL)

FT_PER_M = 1.0 / 0.3048

# Feature types dropped entirely from the output file.
IGNORED_FEATURE_TYPES = {
    'StandardLevelColumn',
    'StandardLevelTable',
    'StandardLevelSector',
}

# Specific features dropped entirely from the output file, by gml:identifier
# UUID: the FIR / UIR airspaces, the STATE (REPUBLIC OF DONLON) and DONLON CIVIL
# AVIATION ADMINISTRATION OrganisationAuthorities, the NOF Unit and the
# GeoBorder.  (Some kept features still reference these; those references are
# left pointing at the original UUIDs and therefore become dangling.)  The value
# is a human-readable label used only in the removal report.
IGNORED_FEATURE_UUIDS = {
    '6118ba76-0d46-4ba7-af63-17f29755e890': 'GeoBorder',
    '709c64da-44e4-47c7-9d57-326a04cbdd3c': 'OrganisationAuthority STATE (REPUBLIC OF DONLON)',
    'c225ae5c-540f-4a48-8867-809b393b2407': 'OrganisationAuthority DONLON CIVIL AVIATION ADMINISTRATION',
    'f4d5e4d4-d84a-481f-b9e3-b359e42c0dff': 'Airspace AMSWELL FIR',
    'b75a32cf-65da-4028-81f2-70ad30072736': 'UIR airspace',
    '6fa9b51a-ea66-40a7-a23a-058c3a034719': 'NOF Unit',
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def is_nil(elem):
    return elem is not None and elem.get(XSI_NIL) == 'true'


def limit_to_feet(value_text, uom):
    """Convert a limit value to feet for comparison, or None if not numeric."""
    try:
        v = float(value_text)
    except (TypeError, ValueError):
        return None
    if uom == 'FL':
        return v * 100.0
    if uom == 'FT':
        return v
    if uom == 'M':
        return v * FT_PER_M
    return None


def set_limit(elem, value_text, uom):
    """Set a limit element's text/uom and clear any xsi:nil / nilReason."""
    elem.text = value_text
    if uom:
        elem.set('uom', uom)
    elif 'uom' in elem.attrib:
        del elem.attrib['uom']
    for attr in (XSI_NIL, 'nilReason'):
        if attr in elem.attrib:
            del elem.attrib[attr]


def make_aixm(local_name, text, tail):
    e = etree.Element(AIXM + local_name)
    e.text = text
    e.tail = tail
    return e


def feature_of(member):
    """Return the single aixm:* feature element inside a message:hasMember."""
    for child in member:
        if isinstance(child.tag, str) and child.tag.startswith(AIXM):
            return child
    return None


def remove_ignored_features(root):
    """Drop every message:hasMember whose feature type is in
    IGNORED_FEATURE_TYPES or whose gml:identifier is in IGNORED_FEATURE_UUIDS.
    Returns (removed_by_type, removed_by_uuid) where removed_by_type is a
    {type_name: count} dict and removed_by_uuid is a list of (uuid, type_name)
    tuples actually removed.  Removing a member keeps the surrounding
    indentation, because each sibling carries the whitespace that precedes the
    next one in its tail."""
    removed_by_type = {}
    removed_by_uuid = []
    for member in list(root.findall(MSG + 'hasMember')):
        feat = feature_of(member)
        if feat is None:
            continue
        local = etree.QName(feat).localname
        ident = feat.find(GML_IDENTIFIER)
        fuuid = ident.text.strip() if ident is not None and ident.text else None
        if fuuid in IGNORED_FEATURE_UUIDS:
            root.remove(member)
            removed_by_uuid.append((fuuid, local))
        elif local in IGNORED_FEATURE_TYPES:
            root.remove(member)
            removed_by_type[local] = removed_by_type.get(local, 0) + 1
    return removed_by_type, removed_by_uuid


# ---------------------------------------------------------------------------
# 1. GND / UNL
# ---------------------------------------------------------------------------


def translate_unl(root):
    """upperLimit UNL -> uom=FL 999.  Done before GND so an UNL sibling makes a
    GND lowerLimit feet-based."""
    n = 0
    for up in root.iter(UPPER):
        if up.text and up.text.strip() == 'UNL':
            set_limit(up, '999', 'FL')
            n += 1
    return n


def translate_gnd(root):
    """lowerLimit GND -> 0, uom=FT if the sibling upperLimit is FT/FL else M."""
    n = 0
    for low in root.iter(LOWER):
        if not (low.text and low.text.strip() == 'GND'):
            continue
        parent = low.getparent()
        up = parent.find(UPPER) if parent is not None else None
        uom = 'FT' if (up is not None and up.get('uom') in ('FT', 'FL')) else 'M'
        set_limit(low, '0', uom)
        n += 1
    return n


# ---------------------------------------------------------------------------
# 2. FLOOR / CEILING
# ---------------------------------------------------------------------------


def _gather_volume_extremes(airspace, uuid_map, seen, lowers, uppers):
    """Collect numeric AirspaceVolume upper/lower limits from an airspace and,
    when a volume is defined by reference (contributorAirspace / theAirspace),
    recurse into the referenced airspaces (the "multiple parts" case)."""
    if id(airspace) in seen:
        return
    seen.add(id(airspace))
    for vol in airspace.iter(AIXM + 'AirspaceVolume'):
        ul = vol.find(UPPER)
        ll = vol.find(LOWER)
        if ul is not None and not is_nil(ul):
            f = limit_to_feet(ul.text, ul.get('uom'))
            if f is not None:
                uppers.append((f, ul.text, ul.get('uom')))
        if ll is not None and not is_nil(ll):
            f = limit_to_feet(ll.text, ll.get('uom'))
            if f is not None:
                lowers.append((f, ll.text, ll.get('uom')))
    for dep in airspace.iter(AIXM + 'theAirspace'):
        href = dep.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            ref = uuid_map.get(href[len('urn:uuid:'):])
            if ref is not None:
                _gather_volume_extremes(ref, uuid_map, seen, lowers, uppers)


def _airspace_volume_extremes(airspace, uuid_map):
    """(lowest_lower, highest_upper) as (value_text, uom) over the airspace's own
    volumes and any referenced contributor airspaces; None when not resolvable."""
    lowers, uppers = [], []
    _gather_volume_extremes(airspace, uuid_map, set(), lowers, uppers)
    lowest = min(lowers)[1:] if lowers else None
    highest = max(uppers)[1:] if uppers else None
    return lowest, highest


def build_airspace_uuid_map(root):
    """{ uuid: Airspace element } for resolving contributorAirspace references."""
    uuid_map = {}
    for member in root.findall(MSG + 'hasMember'):
        airspace = member.find(AIXM + 'Airspace')
        if airspace is None:
            continue
        ident = airspace.find(GML_IDENTIFIER)
        if ident is not None and ident.text:
            uuid_map[ident.text.strip()] = airspace
    return uuid_map


def substitute_airspace_floor_ceiling(root):
    """Replace FLOOR / CEILING tokens inside each Airspace's AirspaceLayers with
    the airspace's overall lowest / highest volume limits."""
    uuid_map = build_airspace_uuid_map(root)
    replaced = 0
    warnings = []
    for member in root.findall(MSG + 'hasMember'):
        airspace = member.find(AIXM + 'Airspace')
        if airspace is None:
            continue
        lowest, highest = _airspace_volume_extremes(airspace, uuid_map)
        for low in airspace.iter(LOWER):
            if low.text and low.text.strip() == 'FLOOR':
                if lowest is None:
                    warnings.append((airspace, 'FLOOR'))
                    continue
                set_limit(low, lowest[0], lowest[1])
                replaced += 1
        for up in airspace.iter(UPPER):
            if up.text and up.text.strip() == 'CEILING':
                if highest is None:
                    warnings.append((airspace, 'CEILING'))
                    continue
                set_limit(up, highest[0], highest[1])
                replaced += 1
    return replaced, warnings


def substitute_routesegment_floor_ceiling(root):
    """Replace FLOOR / CEILING tokens inside each RouteSegment's AirspaceLayers
    with the limits found directly under the RouteSegmentTimeSlice."""
    replaced = 0
    warnings = []
    for member in root.findall(MSG + 'hasMember'):
        rsg = member.find(AIXM + 'RouteSegment')
        if rsg is None:
            continue
        ts = None
        for child in rsg.iter():
            if isinstance(child.tag, str) and 'RouteSegmentTimeSlice' in child.tag:
                ts = child
                break
        if ts is None:
            continue
        direct_up = ts.find(UPPER)
        direct_low = ts.find(LOWER)
        for low in rsg.iter(LOWER):
            if low is direct_low:
                continue
            if low.text and low.text.strip() == 'FLOOR':
                if direct_low is None or is_nil(direct_low) or not direct_low.text:
                    warnings.append((rsg, 'FLOOR'))
                    continue
                set_limit(low, direct_low.text, direct_low.get('uom'))
                replaced += 1
        for up in rsg.iter(UPPER):
            if up is direct_up:
                continue
            if up.text and up.text.strip() == 'CEILING':
                if direct_up is None or is_nil(direct_up) or not direct_up.text:
                    warnings.append((rsg, 'CEILING'))
                    continue
                set_limit(up, direct_up.text, direct_up.get('uom'))
                replaced += 1
    return replaced, warnings


# ---------------------------------------------------------------------------
# 3. Timesheets
# ---------------------------------------------------------------------------


def fix_timesheets(root):
    """Add startDate 01-01 / endDate 31-12 (after timeReference) to every
    non-nil Timesheet that lacks them."""
    n = 0
    for ti in root.iter(TIME_INTERVAL):
        ts = ti.find(TIMESHEET)
        if ts is None:  # xsi:nil timeInterval, nothing to do
            continue
        has_sd = ts.find(START_DATE) is not None
        has_ed = ts.find(END_DATE) is not None
        if has_sd and has_ed:
            continue
        tref = ts.find(TIME_REFERENCE)
        if tref is None:
            continue  # malformed Timesheet, leave as-is
        tail = tref.tail  # indentation that precedes the next sibling
        anchor = tref
        if not has_sd:
            sd = make_aixm('startDate', '01-01', tail)
            ts.insert(list(ts).index(anchor) + 1, sd)
            anchor = sd
        if not has_ed:
            ed = make_aixm('endDate', '31-12', tail)
            ts.insert(list(ts).index(anchor) + 1, ed)
        n += 1
    return n


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------


def write_with_original_header(root, original_path, out_path):
    """Serialise the (modified) tree but keep the original file header
    (declaration + leading comments + root opening tag) byte-for-byte, and write
    with the same newline convention (CRLF/LF) as the original."""
    with open(original_path, 'rb') as f:
        raw = f.read()
    newline = '\r\n' if b'\r\n' in raw else '\n'
    original_text = raw.decode('utf-8').replace('\r\n', '\n')
    body_text = etree.tostring(root, encoding='unicode')
    m_orig = _ROOT_RE.search(original_text)
    m_body = _ROOT_RE.search(body_text)
    if not (m_orig and m_body):
        raise RuntimeError("Could not locate <message:AIXMBasicMessage> root tag.")
    out_text = original_text[:m_orig.end()] + body_text[m_body.end():]
    if not out_text.endswith('\n'):
        out_text += '\n'
    # newline=newline makes Python translate every '\n' in out_text to the
    # original convention on write (out_text contains only '\n' at this point).
    with open(out_path, 'w', encoding='utf-8', newline=newline) as f:
        f.write(out_text)


def _yesno(value):
    v = value.strip().lower()
    if v in ('yes', 'y', 'true', '1'):
        return True
    if v in ('no', 'n', 'false', '0'):
        return False
    raise argparse.ArgumentTypeError(f"expected yes/no, got '{value}'")


def main():
    parser = argparse.ArgumentParser(
        description='Copy a Donlon ALL Baseline AIXM file applying ADM fixes.')
    parser.add_argument('--input', '-i', required=True,
                        help='Path to the input AIXM XML file.')
    parser.add_argument('--output', '-o', default=None,
                        help='Output path (default: <input>_ADM_fix.xml next to '
                             'the input).')
    parser.add_argument('--translate-limits', type=_yesno, default=True,
                        metavar='yes/no',
                        help='Translate GND/UNL/FLOOR/CEILING (default yes).')
    parser.add_argument('--fix-timesheets', type=_yesno, default=True,
                        metavar='yes/no',
                        help='Add startDate 01-01 / endDate 31-12 to Timesheets '
                             'missing them (default yes).')
    args = parser.parse_args()

    if not os.path.isfile(args.input):
        parser.error(f"input file not found: {args.input}")
    if args.output is None:
        stem, ext = os.path.splitext(os.path.abspath(args.input))
        args.output = f"{stem}_ADM_fix{ext or '.xml'}"

    print("Configuration:")
    print(f"  Input:            {args.input}")
    print(f"  Output:           {args.output}")
    print(f"  translate-limits: {'yes' if args.translate_limits else 'no'}")
    print(f"  fix-timesheets:   {'yes' if args.fix_timesheets else 'no'}")
    print()

    print(f"Parsing {args.input} ...")
    tree = etree.parse(args.input)
    root = tree.getroot()

    removed_by_type, removed_by_uuid = remove_ignored_features(root)
    total_removed = sum(removed_by_type.values()) + len(removed_by_uuid)
    print(f"\nIgnored features removed: {total_removed}")
    for name in sorted(IGNORED_FEATURE_TYPES):
        print(f"  {name}: {removed_by_type.get(name, 0)}")
    for fuuid, local in removed_by_uuid:
        print(f"  {local} {fuuid}  ({IGNORED_FEATURE_UUIDS.get(fuuid, '')})")
    removed_uuids = {u for u, _ in removed_by_uuid}
    for fuuid, label in IGNORED_FEATURE_UUIDS.items():
        if fuuid not in removed_uuids:
            print(f"  WARNING: ignore UUID not found in input: {fuuid} ({label})")

    if args.translate_limits:
        n_unl = translate_unl(root)
        n_gnd = translate_gnd(root)
        n_ase, w_ase = substitute_airspace_floor_ceiling(root)
        n_rsg, w_rsg = substitute_routesegment_floor_ceiling(root)
        print("Limit translation:")
        print(f"  UNL  upperLimit -> FL 999:            {n_unl}")
        print(f"  GND  lowerLimit -> 0 (FT/M):          {n_gnd}")
        print(f"  Airspace FLOOR/CEILING replaced:      {n_ase}")
        print(f"  RouteSegment FLOOR/CEILING replaced:  {n_rsg}")
        for elem, token in (w_ase + w_rsg):
            ident = elem.find('{http://www.opengis.net/gml/3.2}identifier')
            uid = ident.text if ident is not None else '?'
            print(f"  WARNING: could not resolve {token} for {uid}")
    else:
        print("Limit translation: skipped")

    if args.fix_timesheets:
        n_ts = fix_timesheets(root)
        print(f"\nTimesheets fixed (startDate/endDate added): {n_ts}")
    else:
        print("\nTimesheet fix: skipped")

    write_with_original_header(root, args.input, args.output)
    print(f"\nDone!  Written {args.output}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
