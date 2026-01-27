#!/usr/bin/env python3
"""
====================================================================
Python script for iNM eEAD - for generating Donlon dataset copies
Source: https://github.com/aixm/Donlon_2025/tree/main/Donlon/DONLON dataset multiplication
Created by: Paul-Adrian LAPUSAN (for EUROCONTROL)
====================================================================
Copyright (c) 2026, EUROCONTROL
=====================================
All rights reserved.
Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
* Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
* Neither the names of EUROCONTROL or FAA nor the names of their contributors may be used to endorse or promote products derived from this specification without specific prior written permission.

THIS SPECIFICATION IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
==========================================
Editorial note: this license is an instance of the BSD license template as
provided by the Open Source Initiative:
http://www.opensource.org/licenses/bsd-license.php
====================================================================

This script generates multiple copies of the following Donlon dataset features:
- Donlon AirportHeliport and associated features
  - Runway, RunwayDirection, RunwayElement, RunwayCentrelinePoint, TouchDownLiftOff
  - Taxiway, TaxiwayElement
  - Apron, ApronElement, AircraftStand
- VerticalStructure
- Navaid and NavaidEquipment
- some Airspace features (types: R, P and D): EAR1, EAV10, EAP2, EAV8, EAD4, EAV11, EAD5 and EAR4
with:
- New designators and names for AirportHeliport (E01D, E02D, etc.), Navaid/NavaidEquipment and VerticalStructure
- New UUIDs for all features
- Updated xlink:href references between copied features
- Geographic positions arranged in a grid pattern

Usage example:
python generate_donlon_dataset_copies.py --grid-rows 5 --grid-cols 6 --distance-nm 30

The input dataset must contain all the features specified above.
The input file is selected on line 646.
"""

import argparse
import copy
import os
import uuid
from lxml import etree

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

NSMAP = {
    'message': 'http://www.aixm.aero/schema/5.1.1/message',
    'gml': 'http://www.opengis.net/gml/3.2',
    'aixm': 'http://www.aixm.aero/schema/5.1.1',
    'xlink': 'http://www.w3.org/1999/xlink',
    'xsi': 'http://www.w3.org/2001/XMLSchema-instance',
}

GML_ID = '{http://www.opengis.net/gml/3.2}id'
XLINK_HREF = '{http://www.w3.org/1999/xlink}href'

EADD_UUID = '1b54b2d6-a5ff-4e57-94c2-f4047a381c64'

# Feature types to extract and clone
FEATURE_TYPES = [
    'AirportHeliport',
    'Runway',
    'RunwayDirection',
    'RunwayElement',
    'RunwayCentrelinePoint',
    'TouchDownLiftOff',
    'Taxiway',
    'TaxiwayElement',
    'Apron',
    'ApronElement',
    'AircraftStand',
    'Navaid',
    'VOR',
    'DME',
    'NDB',
    'TACAN',
    'Localizer',
    'Glidepath',
    'VerticalStructure',
    'Airspace',
]

# NavaidEquipment types (referenced BY Navaids via theNavaidEquipment)
NAVAID_EQUIPMENT_TYPES = ['VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath']

# Airspace designators to copy
AIRSPACE_DESIGNATORS = [
    'EAR1', 'EAV10', 'EAP2', 'EAV8', 'EAD4', 'EAV11', 'EAD5', 'EAR4',
]

# Properties to remove from VerticalStructure copies
VS_PROPERTIES_TO_REMOVE = [
    'hostedPassengerService',
    'supportedGroundLight',
    'hostedSpecialNavStation',
    'hostedUnit',
    'hostedOrganisation',
    'supportedService',
]

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------


def generate_new_uuid():
    return str(uuid.uuid4())


def calculate_grid_offset(index, grid_cols, distance_nm):
    row = index // grid_cols
    col = index % grid_cols
    lat_per_nm = 1.0 / 60.0
    lon_per_nm = 1.0 / (60.0 * 0.6157)  # cos(52°) ≈ 0.6157
    return (row * distance_nm * lat_per_nm,
            col * distance_nm * lon_per_nm)


def offset_coordinate(coord_str, lat_offset, lon_offset):
    parts = coord_str.strip().split()
    if len(parts) >= 2:
        try:
            lat = float(parts[0]) + lat_offset
            lon = float(parts[1]) + lon_offset
            return f"{lat} {lon}"
        except ValueError:
            pass
    return coord_str


def offset_pos_list(pos_list_str, lat_offset, lon_offset, max_line_length=200):
    values = pos_list_str.strip().split()
    coord_pairs = []
    for i in range(0, len(values), 2):
        if i + 1 < len(values):
            try:
                lat = float(values[i]) + lat_offset
                lon = float(values[i + 1]) + lon_offset
                coord_pairs.append(f"{lat} {lon}")
            except ValueError:
                coord_pairs.append(f"{values[i]} {values[i + 1]}")

    lines, current = [], ""
    for pair in coord_pairs:
        test = (current + " " + pair) if current else pair
        if len(test) > max_line_length and current:
            lines.append(current)
            current = pair
        else:
            current = test
    if current:
        lines.append(current)
    return '\n'.join(lines)


# ---------------------------------------------------------------------------
# Feature extraction
# ---------------------------------------------------------------------------


def get_feature_uuid(feature_elem):
    """Return the UUID text from gml:identifier."""
    ident = feature_elem.find('gml:identifier', NSMAP)
    return ident.text.strip() if ident is not None and ident.text else None


def get_xlink_hrefs(feature_elem):
    """Return a set of all UUIDs referenced via xlink:href in urn:uuid: form."""
    uuids = set()
    for elem in feature_elem.iter():
        href = elem.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            uuids.add(href.replace('urn:uuid:', ''))
    return uuids


def extract_features_by_type(root):
    """
    Extract all features from the document, grouped by AIXM type.
    Returns dict: { type_name: { uuid: element } }
    """
    result = {ft: {} for ft in FEATURE_TYPES}
    for member in root.findall('message:hasMember', NSMAP):
        for ft in FEATURE_TYPES:
            elem = member.find(f'aixm:{ft}', NSMAP)
            if elem is not None:
                feat_uuid = get_feature_uuid(elem)
                if feat_uuid:
                    result[ft][feat_uuid] = elem
                break
    return result


def collect_eadd_features(features_by_type):
    """
    Starting from the EADD AirportHeliport, walk the reference chain to
    find all features that belong to this airport.

    Returns dict: { uuid: (type_name, element) } for every feature in scope.
    """
    collected = {}  # uuid -> (type, elem)

    # 1. Start with the EADD airport
    ahp = features_by_type['AirportHeliport'].get(EADD_UUID)
    if ahp is None:
        return collected
    collected[EADD_UUID] = ('AirportHeliport', ahp)

    # Helper: find features of a given type that reference any UUID in target_uuids
    def find_referencing(feat_type, target_uuids):
        found = {}
        for fuuid, felem in features_by_type[feat_type].items():
            if fuuid in collected:
                continue
            refs = get_xlink_hrefs(felem)
            if refs & target_uuids:
                found[fuuid] = felem
        return found

    # 2. Runways -> reference AirportHeliport
    airport_uuids = {EADD_UUID}
    runways = find_referencing('Runway', airport_uuids)
    for u, e in runways.items():
        collected[u] = ('Runway', e)
    runway_uuids = set(runways.keys())

    # 3. RunwayDirection -> reference Runway
    rwy_dirs = find_referencing('RunwayDirection', runway_uuids)
    for u, e in rwy_dirs.items():
        collected[u] = ('RunwayDirection', e)
    rwy_dir_uuids = set(rwy_dirs.keys())

    # 4. RunwayElement -> reference Runway
    rwy_elems = find_referencing('RunwayElement', runway_uuids)
    for u, e in rwy_elems.items():
        collected[u] = ('RunwayElement', e)

    # 5. RunwayCentrelinePoint -> reference RunwayDirection
    rcps = find_referencing('RunwayCentrelinePoint', rwy_dir_uuids)
    for u, e in rcps.items():
        collected[u] = ('RunwayCentrelinePoint', e)

    # 6. TouchDownLiftOff -> reference AirportHeliport (and Runway via approachTakeOffArea)
    tlofs = find_referencing('TouchDownLiftOff', airport_uuids | runway_uuids)
    for u, e in tlofs.items():
        collected[u] = ('TouchDownLiftOff', e)

    # 7. Taxiway -> reference AirportHeliport
    taxiways = find_referencing('Taxiway', airport_uuids)
    for u, e in taxiways.items():
        collected[u] = ('Taxiway', e)
    taxiway_uuids = set(taxiways.keys())

    # 7. TaxiwayElement -> reference Taxiway
    twy_elems = find_referencing('TaxiwayElement', taxiway_uuids)
    for u, e in twy_elems.items():
        collected[u] = ('TaxiwayElement', e)

    # 8. Apron -> reference AirportHeliport
    aprons = find_referencing('Apron', airport_uuids)
    for u, e in aprons.items():
        collected[u] = ('Apron', e)
    apron_uuids = set(aprons.keys())

    # 9. ApronElement -> reference Apron
    apron_elems = find_referencing('ApronElement', apron_uuids)
    for u, e in apron_elems.items():
        collected[u] = ('ApronElement', e)
    apron_elem_uuids = set(apron_elems.keys())

    # 10. AircraftStand -> reference ApronElement (via apronLocation)
    #     or AirportHeliport
    stands = find_referencing('AircraftStand', apron_elem_uuids | airport_uuids)
    for u, e in stands.items():
        collected[u] = ('AircraftStand', e)

    # ---- Navaids and NavaidEquipment (ALL, not just EADD-related) ----

    # Identify EADD-related Navaids/NavaidEquipment (reference any already-collected UUID)
    eadd_uuids_so_far = set(collected.keys())
    eadd_navaid_uuids = set()

    # 11. ALL Navaids — but track which ones are EADD-related
    for fuuid, felem in features_by_type['Navaid'].items():
        if fuuid not in collected:
            refs = get_xlink_hrefs(felem)
            if refs & eadd_uuids_so_far:
                eadd_navaid_uuids.add(fuuid)
            collected[fuuid] = ('Navaid', felem)

    # 12. ALL NavaidEquipment (VOR, DME, NDB, TACAN, Localizer, Glidepath)
    #     EADD-related if they reference any already-collected UUID or an EADD navaid
    eadd_plus_navaid = eadd_uuids_so_far | eadd_navaid_uuids
    for eq_type in NAVAID_EQUIPMENT_TYPES:
        for fuuid, felem in features_by_type[eq_type].items():
            if fuuid not in collected:
                refs = get_xlink_hrefs(felem)
                if refs & eadd_plus_navaid:
                    eadd_navaid_uuids.add(fuuid)
                collected[fuuid] = (eq_type, felem)

    # Also mark equipment referenced by EADD navaids (top-down: Navaid -> theNavaidEquipment)
    for fuuid in list(eadd_navaid_uuids):
        if fuuid in features_by_type.get('Navaid', {}):
            refs = get_xlink_hrefs(features_by_type['Navaid'][fuuid])
            for ref_uuid in refs:
                for eq_type in NAVAID_EQUIPMENT_TYPES:
                    if ref_uuid in features_by_type[eq_type]:
                        eadd_navaid_uuids.add(ref_uuid)

    # ---- VerticalStructure (ALL) ----

    # 13. ALL VerticalStructures
    for fuuid, felem in features_by_type['VerticalStructure'].items():
        if fuuid not in collected:
            collected[fuuid] = ('VerticalStructure', felem)

    # ---- Airspace (selected designators only) ----

    # 14. Airspaces matching AIRSPACE_DESIGNATORS
    for fuuid, felem in features_by_type['Airspace'].items():
        if fuuid in collected:
            continue
        # Find designator in the TimeSlice
        for child in felem.iter():
            tag = child.tag
            if isinstance(tag, str) and 'AirspaceTimeSlice' in tag:
                d = child.find('aixm:designator', NSMAP)
                if d is not None and d.text in AIRSPACE_DESIGNATORS:
                    collected[fuuid] = ('Airspace', felem)
                break

    return collected, eadd_navaid_uuids


# ---------------------------------------------------------------------------
# Feature cloning
# ---------------------------------------------------------------------------


def update_feature_ids(feature_elem, new_uuid):
    """
    Update gml:identifier and all gml:id attributes on a feature element.
    - Feature element:  gml:id = "uuid.<new_uuid>"
    - gml:identifier text = new_uuid
    - TimeSlice:  gml:id = "id_<uuid>_<seq>_<corr>_B"
    - Children of TimeSlice: gml:id = "id_<uuid>_<seq>_<corr>_B_<n>"
    """
    # Feature-level gml:id
    feature_elem.set(GML_ID, f'uuid.{new_uuid}')

    # gml:identifier
    ident = feature_elem.find('gml:identifier', NSMAP)
    if ident is not None:
        ident.text = new_uuid

    # Find the TimeSlice (works for any AIXM type: *TimeSlice)
    timeslice = None
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            timeslice = child
            break

    if timeslice is None:
        return

    # Read sequence / correction numbers
    seq_elem = timeslice.find('aixm:sequenceNumber', NSMAP)
    corr_elem = timeslice.find('aixm:correctionNumber', NSMAP)
    seq = int(seq_elem.text) if seq_elem is not None and seq_elem.text else 1
    corr = int(corr_elem.text) if corr_elem is not None and corr_elem.text else 0

    # TimeSlice gml:id
    timeslice.set(GML_ID, f'id_{new_uuid}_{seq}_{corr}_B')

    # Children of TimeSlice
    child_idx = 1
    for elem in timeslice.iter():
        if elem is timeslice:
            continue
        if elem.get(GML_ID) is not None:
            elem.set(GML_ID, f'id_{new_uuid}_{seq}_{corr}_B_{child_idx}')
            child_idx += 1


def update_xlink_refs(feature_elem, uuid_map):
    """
    Walk the entire element tree and replace any xlink:href urn:uuid:OLD
    with urn:uuid:NEW according to uuid_map.
    """
    for elem in feature_elem.iter():
        href = elem.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            old_uuid = href.replace('urn:uuid:', '')
            if old_uuid in uuid_map:
                elem.set(XLINK_HREF, f'urn:uuid:{uuid_map[old_uuid]}')


def offset_all_coordinates(feature_elem, lat_offset, lon_offset):
    """
    Offset every gml:pos and gml:posList in the feature.
    """
    for pos in feature_elem.iter('{http://www.opengis.net/gml/3.2}pos'):
        if pos.text and pos.text.strip():
            pos.text = offset_coordinate(pos.text, lat_offset, lon_offset)

    for pos_list in feature_elem.iter('{http://www.opengis.net/gml/3.2}posList'):
        if pos_list.text and pos_list.text.strip():
            pos_list.text = offset_pos_list(pos_list.text, lat_offset, lon_offset)


def clone_feature_set(collected_features, index, grid_cols, distance_nm,
                      eadd_navaid_uuids=None):
    """
    Clone a complete set of features for one airport copy.

    Returns a list of (type_name, cloned_element) tuples,
    and the new airport UUID.
    """
    if eadd_navaid_uuids is None:
        eadd_navaid_uuids = set()

    designator = f"E{index + 1:02d}D"
    lat_offset, lon_offset = calculate_grid_offset(index, grid_cols, distance_nm)
    # Reduced offset for non-EADD navaids/equipment (1/10 of normal spacing)
    lat_offset_nav, lon_offset_nav = calculate_grid_offset(
        index, grid_cols, distance_nm / 10.0
    )

    # 1. Build UUID mapping:  old_uuid -> new_uuid
    uuid_map = {}
    for old_uuid in collected_features:
        uuid_map[old_uuid] = generate_new_uuid()

    # 2. Clone each feature
    cloned = []
    for old_uuid, (feat_type, orig_elem) in collected_features.items():
        new_elem = copy.deepcopy(orig_elem)
        new_uuid = uuid_map[old_uuid]

        # Update gml:identifier and all gml:id attributes
        update_feature_ids(new_elem, new_uuid)

        # Update xlink:href references
        update_xlink_refs(new_elem, uuid_map)

        # Offset coordinates — reduced spacing for non-EADD navaids/equipment
        navaid_types = ('Navaid', *NAVAID_EQUIPMENT_TYPES)
        if feat_type in navaid_types and old_uuid not in eadd_navaid_uuids:
            offset_all_coordinates(new_elem, lat_offset_nav, lon_offset_nav)
        else:
            offset_all_coordinates(new_elem, lat_offset, lon_offset)

        # Type-specific updates
        if feat_type == 'AirportHeliport':
            ts = None
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'AirportHeliportTimeSlice' in tag:
                    ts = child
                    break
            if ts is not None:
                # Update designator
                d = ts.find('aixm:designator', NSMAP)
                if d is not None:
                    d.text = designator
                # Update name
                n = ts.find('aixm:name', NSMAP)
                if n is not None:
                    n.text = f"DONLON INTL. {index + 1:02d}"

        # Navaid / NavaidEquipment: append copy suffix to designator and name
        if feat_type in ('Navaid', *NAVAID_EQUIPMENT_TYPES):
            suffix = f"-{index + 1:02d}"
            # Find the TimeSlice (any *TimeSlice child)
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    d = child.find('aixm:designator', NSMAP)
                    if d is not None and d.text:
                        d.text = d.text + suffix
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    break

        # VerticalStructure: suffix name, suffix part designators, remove properties
        if feat_type == 'VerticalStructure':
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    # Append suffix to aixm:name
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    # Append suffix to aixm:designator inside aixm:part
                    #   (only if it has an actual value, not nil)
                    for part_elem in child.iter(
                        '{http://www.aixm.aero/schema/5.1.1}VerticalStructurePart'
                    ):
                        pd = part_elem.find('aixm:designator', NSMAP)
                        if pd is not None and pd.text and pd.text.strip():
                            xsi_nil = pd.get(
                                '{http://www.w3.org/2001/XMLSchema-instance}nil'
                            )
                            if not xsi_nil:
                                pd.text = pd.text + suffix
                    # Remove unwanted properties
                    for prop_name in VS_PROPERTIES_TO_REMOVE:
                        for prop_elem in list(
                            child.findall(f'aixm:{prop_name}', NSMAP)
                        ):
                            child.remove(prop_elem)
                    break

        # Airspace: append suffix to designator and name
        if feat_type == 'Airspace':
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    d = child.find('aixm:designator', NSMAP)
                    if d is not None and d.text:
                        d.text = d.text + suffix
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    break

        cloned.append((feat_type, new_elem))

    return cloned, uuid_map[EADD_UUID]


# ---------------------------------------------------------------------------
# Pretty-print helpers
# ---------------------------------------------------------------------------


def indent_element(elem, level=0, indent_str="  "):
    i = "\n" + level * indent_str
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + indent_str
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for child in elem:
            indent_element(child, level + 1, indent_str)
        if not child.tail or not child.tail.strip():
            child.tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = i
        if elem.text and '\n' in elem.text:
            lines = elem.text.strip().split('\n')
            indented = [lines[0]] + [
                (level + 1) * indent_str + line.strip() for line in lines[1:]
            ]
            elem.text = ('\n' + (level + 1) * indent_str
                         + '\n'.join(indented)
                         + '\n' + level * indent_str)


# ---------------------------------------------------------------------------
# Output document
# ---------------------------------------------------------------------------


OUTPUT_NSMAP = {
    'message': 'http://www.aixm.aero/schema/5.1.1/message',
    'gts': 'http://www.isotc211.org/2005/gts',
    'gco': 'http://www.isotc211.org/2005/gco',
    'xsd': 'http://www.w3.org/2001/XMLSchema',
    'gml': 'http://www.opengis.net/gml/3.2',
    'gss': 'http://www.isotc211.org/2005/gss',
    'aixm': 'http://www.aixm.aero/schema/5.1.1',
    'event': 'http://www.aixm.aero/schema/5.1.1/event',
    'gsr': 'http://www.isotc211.org/2005/gsr',
    'gmd': 'http://www.isotc211.org/2005/gmd',
    'xlink': 'http://www.w3.org/1999/xlink',
    'xsi': 'http://www.w3.org/2001/XMLSchema-instance',
}

SCHEMA_LOCATION = (
    'http://www.aixm.aero/schema/5.1.1/message '
    'http://www.aixm.aero/schema/5.1.1/message/AIXM_BasicMessage.xsd '
    'http://www.aixm.aero/schema/5.1.1/event '
    'https://aixm.aero/schema/5.1.1/event/version_5.1.1-k/Event_Features.xsd'
)


def create_output_document(features, gml_id='Generated_Airports', comment=None):
    """
    Build an AIXM BasicMessage document.
    features: list of (type_name, element) tuples.
    """
    root = etree.Element(
        '{http://www.aixm.aero/schema/5.1.1/message}AIXMBasicMessage',
        nsmap=OUTPUT_NSMAP,
    )
    root.set('{http://www.w3.org/2001/XMLSchema-instance}schemaLocation',
             SCHEMA_LOCATION)
    root.set(GML_ID, gml_id)

    for _feat_type, elem in features:
        member = etree.SubElement(
            root,
            '{http://www.aixm.aero/schema/5.1.1/message}hasMember'
        )
        member.append(elem)

    indent_element(root)
    root.tail = "\n"
    tree = etree.ElementTree(root)
    if comment:
        root.addprevious(etree.Comment(f' {comment} '))
    return tree


def write_xml(tree, path):
    """Write an ElementTree to a file."""
    tree.write(path, encoding='UTF-8', xml_declaration=True, pretty_print=False)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description='Generate multiple copies of Donlon International Airport '
                    'and all associated features'
    )
    parser.add_argument('--input', '-i', default='Donlon_ALL_Baseline.xml')
    parser.add_argument('--output', '-o', default='Donlon_Dataset_Copies')
    parser.add_argument('--grid-rows', '-r', type=int, default=5)
    parser.add_argument('--grid-cols', '-c', type=int, default=6)
    parser.add_argument('--distance-nm', '-d', type=float, default=30.0)
    parser.add_argument('--count', '-n', type=int, default=30)
    args = parser.parse_args()

    count = min(args.count, args.grid_rows * args.grid_cols)

    print("Configuration:")
    print(f"  Input:    {args.input}")
    print(f"  Output:   {args.output}")
    print(f"  Grid:     {args.grid_rows} x {args.grid_cols}")
    print(f"  Distance: {args.distance_nm} NM")
    print(f"  Count:    {count}")
    print()

    # Parse
    print(f"Parsing {args.input} ...")
    tree = etree.parse(args.input)
    root = tree.getroot()

    # Extract all features by type
    print("Extracting features by type ...")
    features_by_type = extract_features_by_type(root)
    for ft in FEATURE_TYPES:
        print(f"  {ft}: {len(features_by_type[ft])} total in file")

    # Collect features belonging to EADD
    print("\nCollecting EADD-related features ...")
    collected, eadd_navaid_uuids = collect_eadd_features(features_by_type)

    # Print summary per type
    type_counts = {}
    for _uuid, (ftype, _elem) in collected.items():
        type_counts[ftype] = type_counts.get(ftype, 0) + 1
    for ft in FEATURE_TYPES:
        c = type_counts.get(ft, 0)
        if c > 0:
            print(f"  {ft}: {c}")
    total_per_copy = len(collected)
    print(f"  TOTAL per copy: {total_per_copy}")

    # Navaid spacing summary
    navaid_eq_types = {'Navaid', *NAVAID_EQUIPMENT_TYPES}
    total_nav = sum(1 for _, (ft, _) in collected.items() if ft in navaid_eq_types)
    eadd_nav = len(eadd_navaid_uuids)
    print(f"  Navaid/Equipment EADD-related: {eadd_nav} (full spacing), "
          f"non-EADD: {total_nav - eadd_nav} (1/10 spacing)")

    # Generate copies
    print(f"\nGenerating {count} copies ({count * total_per_copy} features total) ...")
    all_cloned = []          # flat list of all (type, elem) across all copies
    per_copy_cloned = []     # list of lists, one per copy

    for i in range(count):
        designator = f"E{i + 1:02d}D"
        lat_off, lon_off = calculate_grid_offset(i, args.grid_cols, args.distance_nm)
        print(f"  {designator}:  grid ({i // args.grid_cols},{i % args.grid_cols})  "
              f"offset +{lat_off:.4f}° lat, +{lon_off:.4f}° lon")

        cloned, _new_ahp_uuid = clone_feature_set(
            collected, i, args.grid_cols, args.distance_nm,
            eadd_navaid_uuids=eadd_navaid_uuids
        )
        per_copy_cloned.append(cloned)
        all_cloned.extend(cloned)

    # --- Write outputs into folder structure ---
    out_dir = os.path.abspath(args.output)
    os.makedirs(out_dir, exist_ok=True)

    # 1. ALL features in one file
    all_file = os.path.join(out_dir, 'Donlon_Dataset_Copies_ALL.xml')
    print(f"\nBuilding {all_file} ...")
    all_tree = create_output_document(
        all_cloned,
        gml_id='Donlon_Dataset_Copies_ALL',
        comment='Generated Donlon dataset copies',
    )
    write_xml(all_tree, all_file)
    print(f"  {len(all_cloned)} features written.")

    # 2. Per-copy folders with per-type files
    print(f"\nWriting per-copy folders ...")
    for i, copy_features in enumerate(per_copy_cloned):
        copy_num = i + 1
        copy_dir = os.path.join(out_dir, f'Donlon_Copy_{copy_num:02d}')
        os.makedirs(copy_dir, exist_ok=True)

        # Group features by type
        by_type = {}
        for feat_type, elem in copy_features:
            by_type.setdefault(feat_type, []).append((feat_type, elem))

        for feat_type, feat_list in by_type.items():
            fname = f'{feat_type}_{copy_num:02d}.xml'
            fpath = os.path.join(copy_dir, fname)
            doc = create_output_document(
                feat_list,
                gml_id=f'{feat_type}_Copy_{copy_num:02d}',
                comment=f'{feat_type} features - Copy {copy_num:02d}',
            )
            write_xml(doc, fpath)

        print(f"  Donlon_Copy_{copy_num:02d}/: "
              f"{len(by_type)} type files, {len(copy_features)} features")

    print(f"\nDone!  {len(all_cloned)} features total in {out_dir}")
    return 0


if __name__ == '__main__':
    exit(main())
