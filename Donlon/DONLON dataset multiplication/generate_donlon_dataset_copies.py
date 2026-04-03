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

THIS SPECIFICATION IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
  - all Airspace features (excluding types: FIR, FIR_P, CTA, CTA_P)
with:
  - New designators and names for AirportHeliport (E01D, E02D, etc.), Navaid/NavaidEquipment and VerticalStructure
  - New UUIDs for all features
  - Updated xlink:href references between copied features
  - Geographic positions arranged in a grid pattern

The copies are arranged in a grid pattern with a set distance between each position.

Usage example:
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --grid-rows 5 --grid-cols 6 --distance-nm 30
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --grid-rows 5 --grid-cols 6 --distance-nm 30 --exc-airspace-types CTA CTA_P
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --output Donlon_Dataset_Copies --grid-rows 5 --grid-cols 6 --distance-nm 30
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --grid-rows 5 --grid-cols 6 --distance-nm 30 --effectiveDateStart 2026-04-10T00:00:00Z
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --grid-rows 5 --grid-cols 6 --distance-nm 30 --effectiveDateStart 2026-04-10T00:00:00Z --timeOffset 1-15-05
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --grid-rows 5 --grid-cols 6 --distance-nm 30 --exc-airspace-types CTA CTA_P --effectiveDateStart 2026-04-10T00:00:00Z --timeOffset 1-15-05

Input parameters:
--input -> select the input file path
--output -> (optional) select the output folder; if not specified then the a folder called 'Donlon_Dataset_Copies' will be created by default in the same location as the input file
--grid-rows -> select the horizontal size of the grid
--grid-cols -> select the vertical size of the grid
--distance-nm -> select the horizontal and vertical distance between each grid position
--exc-airspace-types -> (optional) excludes the selected airspace types from being multiplies (FIR and FIR_P are by default excluded)
--effectiveDateStart -> (optional) all features across all copy sets will have the validTime.beginPosition set to the value selected through this parameter
--timeOffset -> (optional) if used in addition to --effectiveDateStart, then the features in the first copy set get the effectiveDateStart time for validTime.beginPosition,
then for each of the remaining copy sets the validTime.beginPosition is incremented by the value specified in timeOffset (days-hours-minutes)

The input dataset must contain all the features specified above.
"""

import argparse
import copy
import math
import os
import re
import uuid
from datetime import datetime, timedelta, timezone
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

# Airspace types always excluded from copying
AIRSPACE_TYPES_EXCLUDE_DEFAULT = {'FIR', 'FIR_P'}

# Output ordering for the All_features file
ALL_FEATURES_ORDER = [
    'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath',
    'AirportHeliport',
    'Airspace',
    'Taxiway', 'TaxiwayElement',
    'Apron', 'ApronElement', 'AircraftStand',
    'Runway', 'RunwayElement', 'RunwayDirection',
    'RunwayCentrelinePoint', 'TouchDownLiftOff',
    'VerticalStructure',
]

# NavaidEquipment types (referenced BY Navaids via theNavaidEquipment)
NAVAID_EQUIPMENT_TYPES = ['VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath']


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
# EPSG:3395 (World Mercator) projection helpers
# ---------------------------------------------------------------------------

_MERCATOR_A = 6378137.0            # WGS84 semi-major axis (metres)
_MERCATOR_E = 0.0818191908426      # WGS84 first eccentricity


def _mercator_forward_y(lat_deg):
    """Latitude (degrees) -> EPSG:3395 northing (Y in metres)."""
    phi = math.radians(lat_deg)
    sin_phi = math.sin(phi)
    return _MERCATOR_A * math.log(
        math.tan(math.pi / 4 + phi / 2)
        * ((1 - _MERCATOR_E * sin_phi) / (1 + _MERCATOR_E * sin_phi))
        ** (_MERCATOR_E / 2)
    )


def _mercator_inverse_y(y):
    """EPSG:3395 northing (Y in metres) -> latitude (degrees). Iterative."""
    t = math.exp(-y / _MERCATOR_A)
    phi = math.pi / 2 - 2 * math.atan(t)
    for _ in range(15):
        sin_phi = math.sin(phi)
        phi_new = math.pi / 2 - 2 * math.atan(
            t * ((1 - _MERCATOR_E * sin_phi) / (1 + _MERCATOR_E * sin_phi))
            ** (_MERCATOR_E / 2)
        )
        if abs(phi_new - phi) < 1e-14:
            break
        phi = phi_new
    return math.degrees(phi)


def offset_mercator_pos_list(pos_list_str, lat_offset, lon_offset,
                             max_line_length=200):
    """
    Offset EPSG:3395 coordinate pairs (X Y in metres) by a geographic
    lat/lon offset (in degrees).  X is easting, Y is northing.
    """
    values = pos_list_str.strip().split()
    delta_x = _MERCATOR_A * math.radians(lon_offset)
    coord_pairs = []
    for i in range(0, len(values), 2):
        if i + 1 < len(values):
            try:
                x = float(values[i])
                y = float(values[i + 1])
                # Y -> lat, apply lat offset, lat -> new Y
                lat = _mercator_inverse_y(y)
                new_y = _mercator_forward_y(lat + lat_offset)
                new_x = x + delta_x
                coord_pairs.append(f"{new_x:.2f} {new_y:.2f}")
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


def get_ref_uuid(feature_elem, ref_element_name):
    """
    Extract the UUID from a specific xlink:href reference element
    (e.g. 'associatedAirportHeliport') inside the feature's TimeSlice.
    Returns the UUID string, or None.
    """
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            ref = child.find(f'aixm:{ref_element_name}', NSMAP)
            if ref is not None:
                href = ref.get(XLINK_HREF)
                if href and href.startswith('urn:uuid:'):
                    return href.replace('urn:uuid:', '')
            break
    return None


def get_airport_name(feature_elem):
    """Extract the name from an AirportHeliport feature's TimeSlice."""
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'AirportHeliportTimeSlice' in tag:
            n = child.find('aixm:name', NSMAP)
            if n is not None and n.text:
                return n.text
            break
    return None


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


def collect_eadd_features(features_by_type, ase_types_exclude=None):
    """
    Collect all features to be cloned and build airport membership mapping.

    Returns:
        collected: { uuid: (type_name, element) }
        airport_membership: { feature_uuid: airport_uuid }
            Maps each airport-related feature to its owning AirportHeliport.
            Features not tied to an airport (Navaid, VerticalStructure, Airspace)
            are not in this dict.
    """
    collected = {}  # uuid -> (type, elem)
    airport_membership = {}  # feature_uuid -> airport_uuid

    # 1. ALL AirportHeliports
    for fuuid, felem in features_by_type['AirportHeliport'].items():
        collected[fuuid] = ('AirportHeliport', felem)
        airport_membership[fuuid] = fuuid  # airport owns itself

    # Intermediate lookup dicts for reference chain resolution
    # Runway -> AirportHeliport
    runway_to_airport = {}
    for fuuid, felem in features_by_type['Runway'].items():
        collected[fuuid] = ('Runway', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            runway_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    # RunwayDirection -> Runway -> AirportHeliport
    rwydir_to_runway = {}
    for fuuid, felem in features_by_type['RunwayDirection'].items():
        collected[fuuid] = ('RunwayDirection', felem)
        rwy_uuid = get_ref_uuid(felem, 'usedRunway')
        if rwy_uuid:
            rwydir_to_runway[fuuid] = rwy_uuid
            ahp_uuid = runway_to_airport.get(rwy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    # RunwayElement -> Runway -> AirportHeliport
    for fuuid, felem in features_by_type['RunwayElement'].items():
        collected[fuuid] = ('RunwayElement', felem)
        rwy_uuid = get_ref_uuid(felem, 'associatedRunway')
        if rwy_uuid:
            ahp_uuid = runway_to_airport.get(rwy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    # RunwayCentrelinePoint -> RunwayDirection -> Runway -> AirportHeliport
    for fuuid, felem in features_by_type['RunwayCentrelinePoint'].items():
        collected[fuuid] = ('RunwayCentrelinePoint', felem)
        rwydir_uuid = get_ref_uuid(felem, 'onRunway')
        if rwydir_uuid:
            rwy_uuid = rwydir_to_runway.get(rwydir_uuid)
            if rwy_uuid:
                ahp_uuid = runway_to_airport.get(rwy_uuid)
                if ahp_uuid:
                    airport_membership[fuuid] = ahp_uuid

    # TouchDownLiftOff -> AirportHeliport
    for fuuid, felem in features_by_type['TouchDownLiftOff'].items():
        collected[fuuid] = ('TouchDownLiftOff', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            airport_membership[fuuid] = ahp_uuid

    # Taxiway -> AirportHeliport
    taxiway_to_airport = {}
    for fuuid, felem in features_by_type['Taxiway'].items():
        collected[fuuid] = ('Taxiway', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            taxiway_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    # TaxiwayElement -> Taxiway -> AirportHeliport
    for fuuid, felem in features_by_type['TaxiwayElement'].items():
        collected[fuuid] = ('TaxiwayElement', felem)
        twy_uuid = get_ref_uuid(felem, 'associatedTaxiway')
        if twy_uuid:
            ahp_uuid = taxiway_to_airport.get(twy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    # Apron -> AirportHeliport
    apron_to_airport = {}
    for fuuid, felem in features_by_type['Apron'].items():
        collected[fuuid] = ('Apron', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            apron_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    # ApronElement -> Apron -> AirportHeliport
    apronelem_to_apron = {}
    for fuuid, felem in features_by_type['ApronElement'].items():
        collected[fuuid] = ('ApronElement', felem)
        apron_uuid = get_ref_uuid(felem, 'associatedApron')
        if apron_uuid:
            apronelem_to_apron[fuuid] = apron_uuid
            ahp_uuid = apron_to_airport.get(apron_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    # AircraftStand -> ApronElement -> Apron -> AirportHeliport
    for fuuid, felem in features_by_type['AircraftStand'].items():
        collected[fuuid] = ('AircraftStand', felem)
        ae_uuid = get_ref_uuid(felem, 'apronLocation')
        if ae_uuid:
            apron_uuid = apronelem_to_apron.get(ae_uuid)
            if apron_uuid:
                ahp_uuid = apron_to_airport.get(apron_uuid)
                if ahp_uuid:
                    airport_membership[fuuid] = ahp_uuid

    # ---- Navaids and NavaidEquipment (ALL) ----
    # Map airport-related Navaids to their airport via:
    #   servedAirport -> AirportHeliport
    #   runwayDirection -> RunwayDirection -> Runway -> AirportHeliport
    #   touchDownLiftOff -> TouchDownLiftOff -> AirportHeliport
    # Build reverse lookup: TouchDownLiftOff UUID -> AirportHeliport UUID
    tdlof_to_airport = {}
    for fuuid, felem in features_by_type['TouchDownLiftOff'].items():
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            tdlof_to_airport[fuuid] = ahp_uuid

    # Collect all Navaids and determine airport membership
    navaid_equipment_refs = {}  # navaid_uuid -> set of equipment UUIDs
    for fuuid, felem in features_by_type['Navaid'].items():
        if fuuid not in collected:
            collected[fuuid] = ('Navaid', felem)
        # Determine airport from servedAirport
        ahp_uuid = get_ref_uuid(felem, 'servedAirport')
        # Try runwayDirection -> Runway -> Airport
        if not ahp_uuid:
            rwydir_uuid = get_ref_uuid(felem, 'runwayDirection')
            if rwydir_uuid:
                rwy_uuid = rwydir_to_runway.get(rwydir_uuid)
                if rwy_uuid:
                    ahp_uuid = runway_to_airport.get(rwy_uuid)
        # Try touchDownLiftOff -> Airport
        if not ahp_uuid:
            tdlof_uuid = get_ref_uuid(felem, 'touchDownLiftOff')
            if tdlof_uuid:
                ahp_uuid = tdlof_to_airport.get(tdlof_uuid)
        if ahp_uuid:
            airport_membership[fuuid] = ahp_uuid
        # Collect referenced NavaidEquipment UUIDs (nested inside NavaidComponent)
        eq_uuids = set()
        for eq_ref in felem.iter(
            '{http://www.aixm.aero/schema/5.1.1}theNavaidEquipment'
        ):
            href = eq_ref.get(XLINK_HREF)
            if href and href.startswith('urn:uuid:'):
                eq_uuids.add(href.replace('urn:uuid:', ''))
        navaid_equipment_refs[fuuid] = eq_uuids

    # Collect all NavaidEquipment and assign airport membership
    # from the parent Navaid
    for eq_type in NAVAID_EQUIPMENT_TYPES:
        for fuuid, felem in features_by_type[eq_type].items():
            if fuuid not in collected:
                collected[fuuid] = (eq_type, felem)
            # If a Navaid that owns this equipment is airport-related,
            # assign the same airport
            for nav_uuid, eq_refs in navaid_equipment_refs.items():
                if fuuid in eq_refs and nav_uuid in airport_membership:
                    airport_membership[fuuid] = airport_membership[nav_uuid]
                    break

    # ---- VerticalStructure (ALL) ----

    # 13. ALL VerticalStructures
    for fuuid, felem in features_by_type['VerticalStructure'].items():
        if fuuid not in collected:
            collected[fuuid] = ('VerticalStructure', felem)

    # ---- Airspace (all except excluded types) ----

    # 14. Airspaces, skipping excluded types
    if ase_types_exclude is None:
        ase_types_exclude = AIRSPACE_TYPES_EXCLUDE_DEFAULT
    for fuuid, felem in features_by_type['Airspace'].items():
        if fuuid in collected:
            continue
        # Check the airspace type in the TimeSlice
        skip = False
        for child in felem.iter():
            tag = child.tag
            if isinstance(tag, str) and 'AirspaceTimeSlice' in tag:
                t = child.find('aixm:type', NSMAP)
                if t is not None and t.text and t.text.strip() in ase_types_exclude:
                    skip = True
                break
        if not skip:
            collected[fuuid] = ('Airspace', felem)

    return collected, airport_membership


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


def parse_time_offset(offset_str):
    """Parse a time offset string in D-HH-MM format and return a timedelta."""
    parts = offset_str.split('-')
    if len(parts) != 3:
        raise ValueError(f"Invalid time offset format '{offset_str}', expected D-HH-MM")
    days = int(parts[0])
    hours = int(parts[1])
    minutes = int(parts[2])
    return timedelta(days=days, hours=hours, minutes=minutes)


def update_valid_time(feature_elem, new_begin_position):
    """
    Set the validTime/TimePeriod/beginPosition text on all TimeSlices
    in the feature to new_begin_position (ISO 8601 string).
    """
    for ts in feature_elem.iter():
        tag = ts.tag
        if not (isinstance(tag, str) and 'TimeSlice' in tag):
            continue
        for bp in ts.iter('{http://www.opengis.net/gml/3.2}beginPosition'):
            bp.text = new_begin_position


def _find_ancestor_srs(parent_map, elem):
    """Walk up the tree via parent_map to find the nearest srsName attribute."""
    node = elem
    while node is not None:
        srs = node.get('srsName')
        if srs:
            return srs
        node = parent_map.get(node)
    return None


def offset_all_coordinates(feature_elem, lat_offset, lon_offset):
    """
    Offset every gml:pos and gml:posList in the feature.
    Handles both EPSG:4326 (geographic) and EPSG:3395 (World Mercator)
    coordinate reference systems.
    """
    # Build a parent map so we can walk up to find srsName
    parent_map = {child: parent for parent in feature_elem.iter()
                  for child in parent}

    for pos in feature_elem.iter('{http://www.opengis.net/gml/3.2}pos'):
        if pos.text and pos.text.strip():
            pos.text = offset_coordinate(pos.text, lat_offset, lon_offset)

    for pos_list in feature_elem.iter('{http://www.opengis.net/gml/3.2}posList'):
        if not (pos_list.text and pos_list.text.strip()):
            continue
        srs = _find_ancestor_srs(parent_map, pos_list)
        if srs and 'EPSG::3395' in srs:
            pos_list.text = offset_mercator_pos_list(
                pos_list.text, lat_offset, lon_offset)
        else:
            pos_list.text = offset_pos_list(
                pos_list.text, lat_offset, lon_offset)


def clone_feature_set(collected_features, airport_membership, index,
                      grid_cols, distance_nm, begin_position=None):
    """
    Clone a complete set of features for one copy set.

    If begin_position is provided (ISO 8601 string), all features in this
    copy set will have their validTime/beginPosition set to that value.

    Returns:
        cloned: list of (type_name, cloned_element) tuples
        new_membership: { new_feature_uuid: new_airport_uuid }
        airport_names: { new_airport_uuid: airport_name_string }
    """

    lat_offset, lon_offset = calculate_grid_offset(index, grid_cols, distance_nm)
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

        # Offset coordinates
        offset_all_coordinates(new_elem, lat_offset, lon_offset)

        # Update validTime beginPosition if specified
        if begin_position is not None:
            update_valid_time(new_elem, begin_position)

        # Type-specific updates
        if feat_type == 'AirportHeliport':
            copy_suffix = f"-{index + 1:02d}"
            ts = None
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'AirportHeliportTimeSlice' in tag:
                    ts = child
                    break
            if ts is not None:
                # Update designator: e.g. EADD -> E01D, EADA -> E01A
                d = ts.find('aixm:designator', NSMAP)
                if d is not None and d.text and len(d.text) >= 2:
                    d.text = f"{d.text[0]}{index + 1:02d}{d.text[-1]}"
                # Update name: e.g. DONLON/INTL -> DONLON/INTL 01
                n = ts.find('aixm:name', NSMAP)
                if n is not None and n.text:
                    n.text = n.text + f" {index + 1:02d}"

        # Navaid / NavaidEquipment: append copy suffix to name only
        if feat_type in ('Navaid', *NAVAID_EQUIPMENT_TYPES):
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
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
                                # OBST-EA-0005-1 -> OBST-EA-5-1-01
                                parts = pd.text.split('-')
                                parts = [p.lstrip('0') or p for p in parts]
                                pd.text = '-'.join(parts) + suffix
                    # Remove unwanted properties
                    for prop_name in VS_PROPERTIES_TO_REMOVE:
                        for prop_elem in list(
                            child.findall(f'aixm:{prop_name}', NSMAP)
                        ):
                            child.remove(prop_elem)
                    break

        # Airspace: append copy set number to designator and name
        if feat_type == 'Airspace':
            copy_suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    d = child.find('aixm:designator', NSMAP)
                    if d is not None and d.text:
                        d.text = d.text + copy_suffix
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + f" {index + 1:02d}"
                    break

        cloned.append((feat_type, new_elem, new_uuid))

    # Build new_membership and airport_names using uuid_map
    new_membership = {}
    airport_names = {}
    for old_uuid, old_airport_uuid in airport_membership.items():
        new_feat_uuid = uuid_map.get(old_uuid)
        new_ahp_uuid = uuid_map.get(old_airport_uuid)
        if new_feat_uuid and new_ahp_uuid:
            new_membership[new_feat_uuid] = new_ahp_uuid

    # Extract airport names from cloned AirportHeliport elements
    for feat_type, elem, new_uuid in cloned:
        if feat_type == 'AirportHeliport':
            name = get_airport_name(elem)
            if name:
                airport_names[new_uuid] = name

    return cloned, new_membership, airport_names


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

    for feat_tuple in features:
        elem = feat_tuple[1]
        member = etree.SubElement(
            root,
            '{http://www.aixm.aero/schema/5.1.1/message}hasMember'
        )
        member.append(elem)

    indent_element(root)
    root.tail = "\n"
    tree = etree.ElementTree(root)
    if comment:
        comment_node = etree.Comment(f' {comment} ')
        comment_node.tail = "\n"
        root.addprevious(comment_node)
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
    parser.add_argument('--input', '-i', required=True,
                        help='Path to the input AIXM XML file')
    parser.add_argument('--output', '-o', default=None,
                        help='Output folder (default: Donlon_Dataset_Copies '
                             'next to the input file)')
    parser.add_argument('--grid-rows', '-r', type=int, default=5)
    parser.add_argument('--grid-cols', '-c', type=int, default=6)
    parser.add_argument('--distance-nm', '-d', type=float, default=30.0)
    parser.add_argument('--exc-airspace-types', nargs='*', default=[],
                        metavar='TYPE',
                        help='Airspace types to exclude from multiplication '
                             '(e.g. P CTA CTA_P). FIR and FIR_P are always excluded.')
    parser.add_argument('--count', '-n', type=int, default=30)
    parser.add_argument('--effectiveDateStart', default=None,
                        help='validTime beginPosition for all copies '
                             '(e.g. 2026-04-10T00:00:00Z)')
    parser.add_argument('--timeOffset', default=None,
                        help='Offset between copy sets in D-HH-MM format '
                             '(e.g. 5-15-00 = 5 days, 15 hours, 0 minutes). '
                             'Requires --effectiveDateStart.')
    args = parser.parse_args()

    # Default output folder: Donlon_Dataset_Copies next to the input file
    if args.output is None:
        input_dir = os.path.dirname(os.path.abspath(args.input))
        args.output = os.path.join(input_dir, 'Donlon_Dataset_Copies')

    count = min(args.count, args.grid_rows * args.grid_cols)

    # Build airspace type exclusion set
    ase_types_exclude = AIRSPACE_TYPES_EXCLUDE_DEFAULT | set(args.exc_airspace_types)

    # Parse effective date and time offset
    effective_start = None
    time_offset = None
    if args.effectiveDateStart:
        effective_start = datetime.fromisoformat(
            args.effectiveDateStart.replace('Z', '+00:00'))
    if args.timeOffset:
        if not args.effectiveDateStart:
            parser.error('--timeOffset requires --effectiveDateStart')
        time_offset = parse_time_offset(args.timeOffset)

    print("Configuration:")
    print(f"  Input:    {args.input}")
    print(f"  Output:   {args.output}")
    print(f"  Grid:     {args.grid_rows} x {args.grid_cols}")
    print(f"  Distance: {args.distance_nm} NM")
    print(f"  Count:    {count}")
    print(f"  Excluded airspace types: {', '.join(sorted(ase_types_exclude))}")
    if effective_start:
        print(f"  Effective date start: {args.effectiveDateStart}")
    if time_offset:
        d = time_offset.days
        h, remainder = divmod(time_offset.seconds, 3600)
        m = remainder // 60
        print(f"  Time offset per copy: {d} day(s) - {h} hr - {m} min")
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

    # Collect all features to clone
    collected, airport_membership = collect_eadd_features(
        features_by_type, ase_types_exclude)
    total_per_copy = len(collected)
    print(f"  TOTAL features per copy: {total_per_copy}")

    # Feature types that always go into Common/
    COMMON_ONLY_TYPES = {'VerticalStructure', 'Airspace'}
    # Feature types that go into airport folders if they have airport membership,
    # otherwise into Common/
    AIRPORT_OR_COMMON_TYPES = {
        'AirportHeliport', 'Runway', 'RunwayDirection', 'RunwayElement',
        'RunwayCentrelinePoint', 'TouchDownLiftOff', 'Taxiway', 'TaxiwayElement',
        'Apron', 'ApronElement', 'AircraftStand',
        'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath',
    }

    # Generate copies
    print(f"\nGenerating {count} copies ({count * total_per_copy} features total) ...")
    all_cloned = []          # flat list of all (type, elem, uuid) across all copies
    per_copy_data = []       # list of (cloned, new_membership, airport_names)

    for i in range(count):
        copy_num = i + 1
        lat_off, lon_off = calculate_grid_offset(i, args.grid_cols, args.distance_nm)

        # Compute beginPosition for this copy set
        copy_begin = None
        if effective_start is not None:
            if time_offset is not None:
                copy_dt = effective_start + time_offset * i
            else:
                copy_dt = effective_start
            copy_begin = copy_dt.strftime('%Y-%m-%dT%H:%M:%SZ')

        time_info = f"  validTime.beginPosition={copy_begin}" if copy_begin else ""
        print(f"  Copy {copy_num:02d}:  grid ({i // args.grid_cols},{i % args.grid_cols})  "
              f"offset +{lat_off:.4f}° lat, +{lon_off:.4f}° lon{time_info}")

        cloned, new_membership, airport_names = clone_feature_set(
            collected, airport_membership, i, args.grid_cols, args.distance_nm,
            begin_position=copy_begin,
        )
        per_copy_data.append((cloned, new_membership, airport_names))
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

    # 2. Per-copy folders
    print(f"\nWriting per-copy folders ...")
    for i, (copy_features, new_membership, airport_names) in enumerate(per_copy_data):
        copy_num = i + 1
        copy_dir = os.path.join(out_dir, f'Donlon_Copy_{copy_num:02d}')
        os.makedirs(copy_dir, exist_ok=True)

        # Separate features into Common and per-airport groups
        common_features = []       # list of (type, elem, uuid)
        airport_features = {}      # airport_uuid -> list of (type, elem, uuid)

        for feat_type, elem, new_uuid in copy_features:
            if feat_type in COMMON_ONLY_TYPES:
                common_features.append((feat_type, elem, new_uuid))
            elif feat_type in AIRPORT_OR_COMMON_TYPES:
                ahp_uuid = new_membership.get(new_uuid)
                if ahp_uuid:
                    airport_features.setdefault(ahp_uuid, []).append(
                        (feat_type, elem, new_uuid))
                else:
                    # No airport association -> Common/
                    common_features.append((feat_type, elem, new_uuid))

        # --- Common/ folder ---
        common_dir = os.path.join(copy_dir, f'Common_{copy_num:02d}')
        os.makedirs(common_dir, exist_ok=True)

        # Group common features by type and write per-type files
        common_by_type = {}
        for feat_type, elem, new_uuid in common_features:
            common_by_type.setdefault(feat_type, []).append(
                (feat_type, elem, new_uuid))

        for feat_type, feat_list in common_by_type.items():
            fname = f'{feat_type}_{copy_num:02d}.xml'
            fpath = os.path.join(common_dir, fname)
            doc = create_output_document(
                feat_list,
                gml_id=f'{feat_type}_Copy_{copy_num:02d}',
                comment=f'{feat_type} features - Copy {copy_num:02d}',
            )
            write_xml(doc, fpath)

        # --- Per-airport folders inside AirportHeliport_related_features_XX ---
        ahp_parent_dir = os.path.join(
            copy_dir, f'AirportHeliport_related_features_{copy_num:02d}')
        os.makedirs(ahp_parent_dir, exist_ok=True)

        for ahp_uuid, ahp_features in airport_features.items():
            # Build folder name from airport name (sanitise for filesystem)
            ahp_name = airport_names.get(ahp_uuid, ahp_uuid)
            # Replace special chars with underscore, collapse runs
            folder_name = re.sub(r'[/\\. ]+', '_', ahp_name).strip('_')
            ahp_dir = os.path.join(ahp_parent_dir, folder_name)
            os.makedirs(ahp_dir, exist_ok=True)

            # Group by type and write per-type files
            ahp_by_type = {}
            for feat_type, elem, new_uuid in ahp_features:
                ahp_by_type.setdefault(feat_type, []).append(
                    (feat_type, elem, new_uuid))

            for feat_type, feat_list in ahp_by_type.items():
                fname = f'{feat_type}_{copy_num:02d}.xml'
                fpath = os.path.join(ahp_dir, fname)
                doc = create_output_document(
                    feat_list,
                    gml_id=f'{feat_type}_Copy_{copy_num:02d}',
                    comment=f'{feat_type} features - Copy {copy_num:02d}',
                )
                write_xml(doc, fpath)

        # --- Donlon_ALL_Baseline.xml (all features, ordered) ---
        ordered_features = []
        for ft in ALL_FEATURES_ORDER:
            for feat_type, elem, new_uuid in copy_features:
                if feat_type == ft:
                    ordered_features.append((feat_type, elem, new_uuid))
        all_feat_path = os.path.join(copy_dir, f'Donlon_ALL_Baseline_{copy_num:02d}.xml')
        all_feat_doc = create_output_document(
            ordered_features,
            gml_id=f'All_features_Copy_{copy_num:02d}',
            comment=f'All features - Copy {copy_num:02d}',
        )
        write_xml(all_feat_doc, all_feat_path)

        airport_folder_count = len(airport_features)
        print(f"  Donlon_Copy_{copy_num:02d}/: Common/ + "
              f"{airport_folder_count} airport folder(s) + Donlon_ALL_Baseline_{copy_num:02d}.xml, "
              f"{len(copy_features)} features")

    print(f"\nDone!  {len(all_cloned)} features total in {out_dir}")
    return 0


if __name__ == '__main__':
    exit(main())
