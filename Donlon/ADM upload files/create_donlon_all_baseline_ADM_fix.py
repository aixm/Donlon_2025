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
   - <aixm:upperLimit>UNL</aixm:upperLimit> -> <aixm:upperLimit uom="FL">999</aixm:upperLimit> with <aixm:upperLimitReference>STD</aixm:upperLimitReference>.
   - <aixm:lowerLimit>GND</aixm:lowerLimit> -> <aixm:lowerLimit>0</aixm:lowerLimit> with the reference taken from the upper limit
        (UNL is translated first, so an UNL sibling counts as FL): upper in FL -> 0 FT, lowerLimitReference MSL; upper in FT/M carrying a
        reference -> 0 with the upper's uom and the same reference.
   - Airspace: <aixm:lowerLimit>FLOOR</aixm:lowerLimit> / <aixm:upperLimit>CEILING</aixm:upperLimit> inside an aixm:AirspaceLayer are
        replaced with the actual value+uom AND reference taken from the airspace's aixm:geometryComponent/aixm:theAirspaceVolume limits.  When the airspace has
        several volumes / parts, FLOOR takes the lowest lowerLimit and CEILING the highest upperLimit (compared in feet), each with its own reference.
   - RouteSegment: FLOOR / CEILING inside an aixm:AirspaceLayer are replaced with the value+uom and reference of the aixm:lowerLimit / aixm:upperLimit found
        directly under the aixm:RouteSegmentTimeSlice.
   - Reference normalisation: any upper/lowerLimit in FL still missing its reference gets STD; an upper in FT/M with a reference propagates it
        to a lower limit that is still missing one.  Existing (non-nil) references (e.g. the MSL vs SFC distinction on FT/M lowers) are never overwritten.

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
UPPER_REF = AIXM + 'upperLimitReference'
LOWER_REF = AIXM + 'lowerLimitReference'
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
    'b75a32cf-65da-4028-81f2-70ad30072736': 'Airspace YORK NEW FIR',
    '6fa9b51a-ea66-40a7-a23a-058c3a034719': 'UIR airspace',
    '895b61a8-e961-4ac1-9994-70c42d4ebf86': 'NOF Unit',
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


def reference_text(ref):
    """The textual value of an upper/lowerLimitReference, or None if the element
    is absent, xsi:nil or empty."""
    if ref is None or ref.get(XSI_NIL) == 'true':
        return None
    return ref.text.strip() if (ref.text and ref.text.strip()) else None


def ref_missing(ref):
    """True when an upper/lowerLimitReference carries no usable value."""
    return reference_text(ref) is None


def set_reference(parent, limit_elem, ref_tag, value):
    """Set the upper/lowerLimitReference (ref_tag) that belongs to limit_elem to
    value, creating it immediately after limit_elem (so the schema order
    upperLimit, upperLimitReference / lowerLimit, lowerLimitReference is kept) if
    it does not exist, and clearing any xsi:nil / nilReason."""
    ref = parent.find(ref_tag)
    if ref is None:
        ref = etree.Element(ref_tag)
        ref.tail = limit_elem.tail
        parent.insert(list(parent).index(limit_elem) + 1, ref)
    ref.text = value
    for attr in (XSI_NIL, 'nilReason'):
        if attr in ref.attrib:
            del ref.attrib[attr]
    return ref


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
    """upperLimit UNL -> uom=FL 999 with upperLimitReference STD.  Done before GND
    so an UNL sibling counts as FL and makes a GND lowerLimit 0 FT MSL."""
    n = 0
    for up in root.iter(UPPER):
        if up.text and up.text.strip() == 'UNL':
            set_limit(up, '999', 'FL')
            parent = up.getparent()
            if parent is not None:
                set_reference(parent, up, UPPER_REF, 'STD')
            n += 1
    return n


def translate_gnd(root):
    """lowerLimit GND -> 0 with its reference taken from the upper limit (UNL is
    already translated to FL by this point):
      - upper in FL  -> lowerLimit 0 FT, lowerLimitReference MSL;
      - upper in FT/M carrying a reference -> lowerLimit 0 <upper uom>,
        lowerLimitReference identical to the upper limit's reference;
      - otherwise (no usable upper) -> 0 (FT if the upper is FT/FL else M), the
        reference left untouched for the final reference pass."""
    n = 0
    for low in root.iter(LOWER):
        if not (low.text and low.text.strip() == 'GND'):
            continue
        parent = low.getparent()
        if parent is None:
            continue
        up = parent.find(UPPER)
        up_uom = up.get('uom') if up is not None else None
        up_ref = reference_text(parent.find(UPPER_REF))
        if up_uom == 'FL':
            set_limit(low, '0', 'FT')
            set_reference(parent, low, LOWER_REF, 'MSL')
        elif up_uom in ('FT', 'M') and up_ref is not None:
            set_limit(low, '0', up_uom)
            set_reference(parent, low, LOWER_REF, up_ref)
        else:
            set_limit(low, '0', 'FT' if up_uom in ('FT', 'FL') else 'M')
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
                uppers.append((f, ul.text, ul.get('uom'), reference_text(vol.find(UPPER_REF))))
        if ll is not None and not is_nil(ll):
            f = limit_to_feet(ll.text, ll.get('uom'))
            if f is not None:
                lowers.append((f, ll.text, ll.get('uom'), reference_text(vol.find(LOWER_REF))))
    for dep in airspace.iter(AIXM + 'theAirspace'):
        href = dep.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            ref = uuid_map.get(href[len('urn:uuid:'):])
            if ref is not None:
                _gather_volume_extremes(ref, uuid_map, seen, lowers, uppers)


def _airspace_volume_extremes(airspace, uuid_map):
    """(lowest_lower, highest_upper) as (value_text, uom, reference) over the
    airspace's own volumes and any referenced contributor airspaces; None when
    not resolvable."""
    lowers, uppers = [], []
    _gather_volume_extremes(airspace, uuid_map, set(), lowers, uppers)
    lowest = min(lowers, key=lambda t: t[0])[1:] if lowers else None
    highest = max(uppers, key=lambda t: t[0])[1:] if uppers else None
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
    the airspace's overall lowest / highest volume limits, copying that volume
    limit's reference (upper/lowerLimitReference) onto the layer as well."""
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
                if lowest[2]:
                    set_reference(low.getparent(), low, LOWER_REF, lowest[2])
                replaced += 1
        for up in airspace.iter(UPPER):
            if up.text and up.text.strip() == 'CEILING':
                if highest is None:
                    warnings.append((airspace, 'CEILING'))
                    continue
                set_limit(up, highest[0], highest[1])
                if highest[2]:
                    set_reference(up.getparent(), up, UPPER_REF, highest[2])
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
        direct_up_ref = reference_text(ts.find(UPPER_REF))
        direct_low_ref = reference_text(ts.find(LOWER_REF))
        for low in rsg.iter(LOWER):
            if low is direct_low:
                continue
            if low.text and low.text.strip() == 'FLOOR':
                if direct_low is None or is_nil(direct_low) or not direct_low.text:
                    warnings.append((rsg, 'FLOOR'))
                    continue
                set_limit(low, direct_low.text, direct_low.get('uom'))
                if direct_low_ref:
                    set_reference(low.getparent(), low, LOWER_REF, direct_low_ref)
                replaced += 1
        for up in rsg.iter(UPPER):
            if up is direct_up:
                continue
            if up.text and up.text.strip() == 'CEILING':
                if direct_up is None or is_nil(direct_up) or not direct_up.text:
                    warnings.append((rsg, 'CEILING'))
                    continue
                set_limit(up, direct_up.text, direct_up.get('uom'))
                if direct_up_ref:
                    set_reference(up.getparent(), up, UPPER_REF, direct_up_ref)
                replaced += 1
    return replaced, warnings


# ---------------------------------------------------------------------------
# 3. Limit reference normalisation (FL -> STD; FT/M upper -> lower)
# ---------------------------------------------------------------------------

# Parents that carry an upper/lowerLimit + reference pair handled by the rules.
_LIMIT_PARENTS = {
    'AirspaceLayer', 'AirspaceVolume', 'RouteSegmentTimeSlice',
    'HoldingPatternTimeSlice',
}


def finalize_limit_references(root):
    """After the value translations, fill any still-missing upper/lowerLimit
    reference:
      - a limit expressed in FL gets reference STD;
      - when the upper limit is in FT/M and carries a reference, a lower limit
        still missing its reference inherits the upper limit's reference.
    Existing (non-nil) references are never overwritten.  Returns
    (fl_to_std_count, inherited_count)."""
    fl_std = 0
    inherited = 0
    for parent in root.iter():
        if not isinstance(parent.tag, str):
            continue
        if etree.QName(parent).localname not in _LIMIT_PARENTS:
            continue
        ul = parent.find(UPPER)
        ll = parent.find(LOWER)
        for lim, ref_tag in ((ul, UPPER_REF), (ll, LOWER_REF)):
            if lim is None or is_nil(lim):
                continue
            if lim.get('uom') == 'FL' and ref_missing(parent.find(ref_tag)):
                set_reference(parent, lim, ref_tag, 'STD')
                fl_std += 1
        if (ul is not None and not is_nil(ul) and ul.get('uom') in ('FT', 'M')
                and ll is not None and not is_nil(ll)):
            up_ref = reference_text(parent.find(UPPER_REF))
            if up_ref and ref_missing(parent.find(LOWER_REF)):
                set_reference(parent, ll, LOWER_REF, up_ref)
                inherited += 1
    return fl_std, inherited


# ---------------------------------------------------------------------------
# 4. Timesheets
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
                        help='Output path (default: <input-name>_ADM_upload.xml next '
                             'to this script).')
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
        script_dir = os.path.dirname(os.path.abspath(__file__))
        name, ext = os.path.splitext(os.path.basename(args.input))
        args.output = os.path.join(script_dir, f"{name}_ADM_upload{ext or '.xml'}")

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
        n_fl_std, n_inherited = finalize_limit_references(root)
        print("Limit translation:")
        print(f"  UNL  upperLimit -> FL 999 STD:        {n_unl}")
        print(f"  GND  lowerLimit -> 0 (FT/M) + ref:    {n_gnd}")
        print(f"  Airspace FLOOR/CEILING replaced:      {n_ase}")
        print(f"  RouteSegment FLOOR/CEILING replaced:  {n_rsg}")
        print(f"  FL limits given reference STD:        {n_fl_std}")
        print(f"  Lower refs inherited from upper:      {n_inherited}")
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
