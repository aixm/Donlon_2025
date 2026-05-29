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
  - DesignatedPoint
  - all Airspace features
with:
  - New designators and names for AirportHeliport (E01D, E02D, etc.), Navaid/NavaidEquipment and VerticalStructure
  - New UUIDs for all features
  - Updated xlink:href references between copied features
  - Geographic positions kept inside the EAAD FIR

DesignatedPoint copies keep their original name and designator unchanged.

Layout strategy: EAAD FIR is enclosed in its axis-aligned bounding
rectangle; the rectangle is split in four around the FIR centre.  The
source AirportHeliport ARP sits in one of the four quarters and copies
fill a grid that starts at the source cell and grows toward the opposite
corner of the bbox, spaced by --distance-nm in both lat and lon.

Copy 1 is kept at the original position.  Cells fill row-by-row from the
source corner: the source row first (cols_per_row cells), then the next
row inward, and so on, until --number-of-copies cells have been placed.

For example, source feature `x` situated in the lower-right quarter of the FIR bbox, accommodating a 5x5 grid:

o o o o o
o o o o o
o o o o o
o o o o o
o o o o x

With --number-of-copies 12 the grid fills like:

o o
o o o o o
o o o o x

Usage example:
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --number-of-copies 15 --distance-nm 30
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --number-of-copies 15 --distance-nm 30 --exc-airspace-types FIR UIR CTA CTA_P AWY ADIZ
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --output Donlon_Dataset_Copies --number-of-copies 15 --distance-nm 30
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --number-of-copies 15 --distance-nm 30 --effectiveDateStart 2026-06-02T00:00:00Z
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --number-of-copies 15 --distance-nm 30 --effectiveDateStart 2026-06-02T00:00:00Z --timeOffset 1-15-05
OR
  python generate_donlon_dataset_copies.py --input Donlon_ALL_Baseline.xml --number-of-copies 15 --distance-nm 30 --exc-airspace-types FIR UIR CTA CTA_P AWY ADIZ --exc-features EAA1 EAX4 EAX5 EAHTZCB EAV1 EAV2 EAV3 SAGON ILIDA ATLIM BISBO ILURU UKORO AL ALM --effectiveDateStart 2026-06-02T00:00:00Z --timeOffset 1-15-05

Input parameters:
--input -> select the input file path
--output -> (optional) select the output folder; if not specified then the a folder called 'Donlon_Dataset_Copies' will be created by default in the same location as the input file
--number-of-copies -> number of copy sets to generate (laid out in a line inside the EAAD FIR bounding rectangle)
--distance-nm -> distance between successive copies along the chosen axis
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
import sys
import uuid
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from lxml import etree

# Counter for xlink references that are intentionally not carried over to
# clones (replaced with xsi:nil).  Keyed by (feature_type, property_name).
# Populated via record_excluded_ref(); summary printed by
# print_excluded_refs_summary().
EXCLUDED_REF_LOG = defaultdict(int)


def record_excluded_ref(feature_type, property_name, count=1):
    """Record that `count` xlink reference(s) under aixm:<property_name> were
    removed (replaced with xsi:nil) on a cloned <feature_type> feature."""
    EXCLUDED_REF_LOG[(feature_type, property_name)] += count


def print_excluded_refs_summary():
    """Print one line per (feature_type, property_name) pair whose references
    were excluded across all generated copies."""
    if not EXCLUDED_REF_LOG:
        return
    print("\nExcluded xlink references (replaced with xsi:nil):")
    for (ftype, prop), n in sorted(EXCLUDED_REF_LOG.items()):
        print(f"  {prop} reference excluded from {ftype} feature: "
              f"{n} occurrence(s)")

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
    'MarkerBeacon',
    'DesignatedPoint',
    'VerticalStructure',
    'Airspace',
]

# Airspace types always excluded from copying
AIRSPACE_TYPES_EXCLUDE_DEFAULT = {'FIR', 'FIR_P'}

# Output ordering for the All_features file
ALL_FEATURES_ORDER = [
    'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon',
    'DesignatedPoint',
    'AirportHeliport',
    'Airspace',
    'Taxiway', 'TaxiwayElement',
    'Apron', 'ApronElement', 'AircraftStand',
    'Runway', 'RunwayElement', 'RunwayDirection',
    'RunwayCentrelinePoint', 'TouchDownLiftOff',
    'VerticalStructure',
]

# NavaidEquipment types (referenced BY Navaids via theNavaidEquipment)
NAVAID_EQUIPMENT_TYPES = ['VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon']


# Properties to remove from VerticalStructure copies
VS_PROPERTIES_TO_REMOVE = [
    'hostedPassengerService',
    'supportedGroundLight',
    'hostedSpecialNavStation',
    'hostedUnit',
    'hostedOrganisation',
    'supportedService',
]

# AirportHeliport designator prefixes by name substring (case-insensitive).
# Each copy uses prefix + a letter starting from 'A' (copy 1 = A, copy 2 = B,
# ...).  Order matters: more specific names must come first.
AIRPORT_DESIGNATOR_PREFIX = [
    ('DONLON/DOWNTOWN HELIPORT', 'EAH'),
    ('DONLON/INTL',              'EAD'),
    ('MAGNETO',                  'EAM'),
    ('AKVIN',                    'EAK'),
]
MAX_AIRPORT_COPIES = 26  # A..Z


def get_airport_designator_prefix(name):
    """Return the 3-letter designator prefix for an AirportHeliport name,
    or None if no mapping is configured for that name."""
    if not name:
        return None
    up = name.upper()
    for key, prefix in AIRPORT_DESIGNATOR_PREFIX:
        if key in up:
            return prefix
    return None

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------


def generate_new_uuid():
    return str(uuid.uuid4())


def _quarter_name(in_upper, in_right):
    if in_upper and in_right:
        return 'TR (NE)'
    if in_upper and not in_right:
        return 'TL (NW)'
    if not in_upper and in_right:
        return 'BR (SE)'
    return 'BL (SW)'


def haversine_distance_nm(lat1, lon1, lat2, lon2):
    """Great-circle distance in nautical miles between two points (degrees)."""
    R_nm = 3440.065
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlam = math.radians(lon2 - lon1)
    a = (math.sin(dphi / 2) ** 2
         + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2)
    return 2 * R_nm * math.asin(math.sqrt(a))


# Border-proximity safety: any feature within this many NM of the FIR
# polygon edge is shifted BORDER_SHIFT_NM toward the opposite corner of
# its own quadrant before its copies are emitted.
BORDER_PROXIMITY_NM = 5.0
BORDER_SHIFT_NM = 5.0


def _point_to_segment_distance_nm(plat, plon, lat1, lon1, lat2, lon2):
    """Approx. distance (NM) from point (plat, plon) to segment ((lat1,lon1),
    (lat2,lon2)) using an equirectangular projection centred on the point.
    Adequate for short distances (< a few hundred NM)."""
    cos_lat = math.cos(math.radians(plat))
    x1 = (lon1 - plon) * 60.0 * cos_lat
    y1 = (lat1 - plat) * 60.0
    x2 = (lon2 - plon) * 60.0 * cos_lat
    y2 = (lat2 - plat) * 60.0
    dx, dy = x2 - x1, y2 - y1
    if dx == 0 and dy == 0:
        return math.hypot(x1, y1)
    t = -(x1 * dx + y1 * dy) / (dx * dx + dy * dy)
    t = max(0.0, min(1.0, t))
    cx = x1 + t * dx
    cy = y1 + t * dy
    return math.hypot(cx, cy)


def distance_to_polygon_nm(plat, plon, polygon):
    """Minimum perpendicular distance (NM) from a point to any edge of the
    closed polygon (a list of (lat, lon) tuples)."""
    if not polygon or len(polygon) < 2:
        return float('inf')
    min_d = float('inf')
    for i in range(len(polygon) - 1):
        lat1, lon1 = polygon[i]
        lat2, lon2 = polygon[i + 1]
        d = _point_to_segment_distance_nm(plat, plon, lat1, lon1, lat2, lon2)
        if d < min_d:
            min_d = d
    if polygon[0] != polygon[-1]:
        lat1, lon1 = polygon[-1]
        lat2, lon2 = polygon[0]
        d = _point_to_segment_distance_nm(plat, plon, lat1, lon1, lat2, lon2)
        if d < min_d:
            min_d = d
    return min_d


def iter_feature_geographic_vertices(feature_elem):
    """Yield (lat, lon) tuples for every EPSG:4326 vertex carried by a
    feature element.  Projected coordinates (EPSG:3395 metres, etc.) and
    values outside the geographic range are skipped."""
    for pos in feature_elem.iter('{http://www.opengis.net/gml/3.2}pos'):
        if not (pos.text and pos.text.strip()):
            continue
        parts = pos.text.strip().split()
        if len(parts) >= 2:
            try:
                lat, lon = float(parts[0]), float(parts[1])
            except ValueError:
                continue
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                yield lat, lon
    for pos_list in feature_elem.iter(
            '{http://www.opengis.net/gml/3.2}posList'):
        if not (pos_list.text and pos_list.text.strip()):
            continue
        vals = pos_list.text.strip().split()
        for i in range(0, len(vals) - 1, 2):
            try:
                lat, lon = float(vals[i]), float(vals[i + 1])
            except ValueError:
                continue
            if -90 <= lat <= 90 and -180 <= lon <= 180:
                yield lat, lon


def min_feature_distance_to_polygon_nm(feature_elem, polygon):
    """Smallest distance (NM) from any of a feature's geographic vertices to
    the polygon edge.  Returns +inf if the feature has no usable geographic
    coordinates."""
    if not polygon or len(polygon) < 2:
        return float('inf')
    min_d = float('inf')
    for lat, lon in iter_feature_geographic_vertices(feature_elem):
        d = distance_to_polygon_nm(lat, lon, polygon)
        if d < min_d:
            min_d = d
            if min_d == 0.0:
                break
    return min_d


def compute_grid_layout(bbox, anchor_lat, anchor_lon, distance_nm):
    """
    Build a grid that starts at the source anchor (placed in one corner cell)
    and grows toward the opposite corner of the FIR bounding rectangle.

    bbox is (min_lat, max_lat, min_lon, max_lon).  The source quarter is
    determined by comparing the anchor to the FIR centre (bbox midpoint).
    Row 0 / col 0 is the anchor; rows fill toward the opposite lat-half,
    cols toward the opposite lon-half, both spaced by --distance-nm.

    Returns a dict with:
        lat_sign, lon_sign : +/-1 grid growth direction
        max_rows, max_cols : highest valid row/col index that stays inside bbox
        d_lat, d_lon       : grid spacing in degrees
        quarter            : human label for the source quarter
    """
    min_lat, max_lat, min_lon, max_lon = bbox
    lat_mid = (min_lat + max_lat) / 2
    lon_mid = (min_lon + max_lon) / 2

    in_upper = anchor_lat >= lat_mid
    in_right = anchor_lon >= lon_mid

    lat_per_nm = 1.0 / 60.0
    cos_lat = math.cos(math.radians(anchor_lat))
    lon_per_nm = 1.0 / (60.0 * cos_lat) if abs(cos_lat) > 1e-6 else 1.0 / 60.0

    d_lat = distance_nm * lat_per_nm
    d_lon = distance_nm * lon_per_nm

    lat_sign = -1 if in_upper else +1
    lon_sign = -1 if in_right else +1

    room_lat_deg = (max_lat - anchor_lat) if lat_sign > 0 else (anchor_lat - min_lat)
    room_lon_deg = (max_lon - anchor_lon) if lon_sign > 0 else (anchor_lon - min_lon)
    room_lat_deg = max(0.0, room_lat_deg)
    room_lon_deg = max(0.0, room_lon_deg)

    max_rows = int(room_lat_deg / d_lat) if d_lat > 0 else 0
    max_cols = int(room_lon_deg / d_lon) if d_lon > 0 else 0

    return {
        'lat_sign': lat_sign,
        'lon_sign': lon_sign,
        'max_rows': max_rows,
        'max_cols': max_cols,
        'd_lat': d_lat,
        'd_lon': d_lon,
        'quarter': _quarter_name(in_upper, in_right),
    }


def choose_cols_per_row(number_of_copies, layout):
    """
    Pick a row width that produces a roughly square grid for the requested
    number of copies, capped by the columns that still fit inside the FIR
    bbox at the current --distance-nm spacing.
    """
    bbox_limit = max(1, layout['max_cols'] + 1)
    desired = max(1, math.ceil(math.sqrt(max(1, number_of_copies))))
    return min(desired, bbox_limit)


def calculate_grid_position(index, layout, cols_per_row):
    """
    (lat_offset_deg, lon_offset_deg) for the (index)-th copy, 0-based.

    Cells fill row-by-row: the source row (row 0) is filled across all
    `cols_per_row` columns, then row 1, etc.  Within a row the column index
    runs from 0 (source column) outward.
    """
    if cols_per_row < 1:
        cols_per_row = 1
    row = index // cols_per_row
    col = index % cols_per_row
    return (row * layout['d_lat'] * layout['lat_sign'],
            col * layout['d_lon'] * layout['lon_sign'])


def determine_feature_signs(feat_lat, feat_lon, bbox, anchor_lat, anchor_lon,
                            anchor_lat_sign, anchor_lon_sign, threshold_nm=90.0):
    """
    Grid growth direction for a single feature.

    Features within *threshold_nm* of the anchor follow the anchor's
    direction.  Features farther away use their own quadrant (relative to
    the FIR bbox centre) so that copies spread outward in every direction.
    """
    dist = haversine_distance_nm(feat_lat, feat_lon, anchor_lat, anchor_lon)
    if dist <= threshold_nm:
        return anchor_lat_sign, anchor_lon_sign
    min_lat, max_lat, min_lon, max_lon = bbox
    lat_mid = (min_lat + max_lat) / 2
    lon_mid = (min_lon + max_lon) / 2
    lat_sign = -1 if feat_lat >= lat_mid else +1
    lon_sign = -1 if feat_lon >= lon_mid else +1
    return lat_sign, lon_sign


def find_fir_polygon(root, designator='EAAD'):
    """
    Return the polygon of the Airspace with type=FIR and the given designator
    as a list of (lat, lon) tuples, or None if not found.
    """
    for member in root.findall('message:hasMember', NSMAP):
        airspace = member.find('aixm:Airspace', NSMAP)
        if airspace is None:
            continue
        for ts in airspace.iter():
            tag = ts.tag
            if not (isinstance(tag, str) and 'AirspaceTimeSlice' in tag):
                continue
            t = ts.find('aixm:type', NSMAP)
            if t is None or t.text != 'FIR':
                break
            d = ts.find('aixm:designator', NSMAP)
            if designator and (d is None or d.text != designator):
                break
            for pos_list in ts.iter('{http://www.opengis.net/gml/3.2}posList'):
                text = pos_list.text
                if not text:
                    continue
                values = text.strip().split()
                polygon = []
                for i in range(0, len(values) - 1, 2):
                    try:
                        polygon.append((float(values[i]), float(values[i + 1])))
                    except ValueError:
                        pass
                if polygon:
                    return polygon
            break
    return None


def find_anchor_position(root):
    """
    Return (lat, lon) of the first AirportHeliport's ARP in the source dataset,
    or None if no AirportHeliport with an ARP is present.
    """
    for member in root.findall('message:hasMember', NSMAP):
        ahp = member.find('aixm:AirportHeliport', NSMAP)
        if ahp is None:
            continue
        for arp in ahp.iter('{http://www.aixm.aero/schema/5.1.1}ARP'):
            for pos in arp.iter('{http://www.opengis.net/gml/3.2}pos'):
                if pos.text:
                    parts = pos.text.strip().split()
                    if len(parts) >= 2:
                        try:
                            return float(parts[0]), float(parts[1])
                        except ValueError:
                            pass
    return None


def get_feature_position(feature_elem):
    """Return (lat, lon) representative position of a feature, or None.

    Scans gml:pos and gml:posList elements for the first geographic
    coordinate pair (EPSG:4326 range).  Projected coordinates (e.g.
    EPSG:3395 values in metres) are skipped automatically.
    """
    for pos in feature_elem.iter('{http://www.opengis.net/gml/3.2}pos'):
        if pos.text and pos.text.strip():
            parts = pos.text.strip().split()
            if len(parts) >= 2:
                try:
                    lat, lon = float(parts[0]), float(parts[1])
                    if -90 <= lat <= 90 and -180 <= lon <= 180:
                        return lat, lon
                except ValueError:
                    pass
    for pos_list in feature_elem.iter('{http://www.opengis.net/gml/3.2}posList'):
        if pos_list.text and pos_list.text.strip():
            values = pos_list.text.strip().split()
            if len(values) >= 2:
                try:
                    lat, lon = float(values[0]), float(values[1])
                    if -90 <= lat <= 90 and -180 <= lon <= 180:
                        return lat, lon
                except ValueError:
                    pass
    return None


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


def get_feature_designator(feature_elem):
    """Return the aixm:designator text from the feature's TimeSlice, or None."""
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            d = child.find('aixm:designator', NSMAP)
            if d is not None and d.text:
                return d.text.strip()
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

    # ---- DesignatedPoint (ALL) ----
    for fuuid, felem in features_by_type['DesignatedPoint'].items():
        if fuuid not in collected:
            collected[fuuid] = ('DesignatedPoint', felem)

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
                      grid_row, grid_col, layout, bbox,
                      anchor_lat, anchor_lon, threshold_nm=90.0,
                      begin_position=None,
                      border_near_uuids=None):
    """
    Clone a complete set of features for one copy set.

    Each feature's offset direction is determined by its own quadrant inside
    the FIR bounding box.  Features within *threshold_nm* of the anchor
    (EADD ARP) share the anchor's direction; features farther away use their
    own quadrant so that copies spread outward in every direction.

    Returns:
        cloned: list of (type_name, cloned_element) tuples
        new_membership: { new_feature_uuid: new_airport_uuid }
        airport_names: { new_airport_uuid: airport_name_string }
    """

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

        # Per-feature offset based on original position and quadrant
        feat_pos = get_feature_position(orig_elem)
        if feat_pos:
            f_lat_sign, f_lon_sign = determine_feature_signs(
                feat_pos[0], feat_pos[1], bbox,
                anchor_lat, anchor_lon,
                layout['lat_sign'], layout['lon_sign'],
                threshold_nm)
        else:
            f_lat_sign = layout['lat_sign']
            f_lon_sign = layout['lon_sign']
        lat_offset = grid_row * layout['d_lat'] * f_lat_sign
        lon_offset = grid_col * layout['d_lon'] * f_lon_sign

        # Border-proximity safety nudge: features within BORDER_PROXIMITY_NM
        # of the FIR polygon edge get an extra BORDER_SHIFT_NM inward offset
        # (direction matches the feature's quadrant signs) applied to every
        # copy, including copy 1.
        if border_near_uuids and old_uuid in border_near_uuids and feat_pos:
            extra_d_lat = BORDER_SHIFT_NM / 60.0
            extra_d_lon = BORDER_SHIFT_NM / (
                60.0 * max(math.cos(math.radians(feat_pos[0])), 1e-6)
            )
            lat_offset += extra_d_lat * f_lat_sign
            lon_offset += extra_d_lon * f_lon_sign

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
                # Resolve the per-airport designator prefix from the ORIGINAL
                # name before we suffix it.  Copy 1 -> 'A', copy 2 -> 'B', ...
                n = ts.find('aixm:name', NSMAP)
                original_name = n.text if (n is not None and n.text) else None
                prefix = get_airport_designator_prefix(original_name)
                d = ts.find('aixm:designator', NSMAP)
                if d is not None and d.text and len(d.text) >= 2:
                    if prefix:
                        d.text = f"{prefix}{chr(ord('A') + index)}"
                    else:
                        # No mapping for this airport name; keep the source
                        # designator unchanged on copy 1 and step the last
                        # character A/B/C... on subsequent copies
                        # (e.g. EA00A -> EA00A, EA00B, EA00C ...).
                        d.text = f"{d.text[:-1]}{chr(ord('A') + index)}"
                    # Keep aixm:locationIndicatorICAO aligned with the new
                    # designator on every copy, but only where the source had
                    # an actual value (leave xsi:nil entries untouched).
                    li = ts.find('aixm:locationIndicatorICAO', NSMAP)
                    if li is not None and li.text and li.text.strip():
                        li.text = d.text
                # Update name: e.g. DONLON/INTL -> DONLON/INTL 01
                if n is not None and n.text:
                    n.text = n.text + f" {index + 1:02d}"
            # AltimeterSource is not cloned, so replace any
            # aixm:altimeterSource xlink reference with xsi:nil.
            xlink_href = '{http://www.w3.org/1999/xlink}href'
            xsi_nil = '{http://www.w3.org/2001/XMLSchema-instance}nil'
            alt_tag = '{http://www.aixm.aero/schema/5.1.1}altimeterSource'
            for asrc in new_elem.iter(alt_tag):
                if asrc.get(xlink_href):
                    tail = asrc.tail
                    asrc.clear()
                    asrc.tail = tail
                    asrc.set(xsi_nil, 'true')
                    record_excluded_ref('AirportHeliport', 'altimeterSource')

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

        # DesignatedPoint: keep original designator and name unchanged on copies

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
                    # Cloned airspaces are not ICAO-published.
                    di = child.find('aixm:designatorICAO', NSMAP)
                    if di is not None:
                        di.text = 'NO'
                        # Remove any xsi:nil/nilReason that the source carried.
                        for attr in (
                            '{http://www.w3.org/2001/XMLSchema-instance}nil',
                            'nilReason',
                        ):
                            if attr in di.attrib:
                                del di.attrib[attr]
                    break

        # ApronElement: AirportSuppliesService is not cloned, so replace any
        # aixm:supplyService xlink reference with xsi:nil to avoid dangling refs.
        if feat_type == 'ApronElement':
            xlink_href = '{http://www.w3.org/1999/xlink}href'
            xsi_nil = '{http://www.w3.org/2001/XMLSchema-instance}nil'
            supply_tag = '{http://www.aixm.aero/schema/5.1.1}supplyService'
            for ss in new_elem.iter(supply_tag):
                if ss.get(xlink_href):
                    tail = ss.tail
                    ss.clear()
                    ss.tail = tail
                    ss.set(xsi_nil, 'true')
                    record_excluded_ref('ApronElement', 'supplyService')

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


_HEADER_RE = re.compile(
    r"(<\?xml[^?]*\?>)\s*(<!--.*?-->)?\s*"
    r"(<message:AIXMBasicMessage)([^>]*)>",
    re.DOTALL,
)
_ATTR_RE = re.compile(r'(\S+?="[^"]*")')


def _format_root_header(path):
    """Re-format the AIXMBasicMessage opening tag so the leading comment sits
    on its own line and namespace declarations / schemaLocation / gml:id each
    sit on their own indented line, matching the reference style.
    """
    with open(path, encoding='utf-8') as f:
        text = f.read()
    m = _HEADER_RE.match(text)
    if not m:
        return
    xml_decl, comment, open_tag, attrs_blob = m.groups()
    attrs = _ATTR_RE.findall(attrs_blob)
    if not attrs:
        return
    formatted = []
    for a in attrs:
        if a.startswith('xsi:schemaLocation='):
            name, _, val = a.partition('=')
            tokens = val.strip('"').split()
            pairs = [' '.join(tokens[i:i + 2]) for i in range(0, len(tokens), 2)]
            formatted.append(f'{name}="' + ' \n  '.join(pairs) + '"')
        else:
            formatted.append(a)
    header = f'{xml_decl}\n'
    if comment:
        header += f'{comment}\n'
    header += f'{open_tag} \n  ' + ' \n  '.join(formatted) + '>'
    new_text = header + text[m.end():]
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(new_text)


def write_xml(tree, path):
    """Write an ElementTree to a file."""
    tree.write(path, encoding='UTF-8', xml_declaration=True, pretty_print=False)
    _format_root_header(path)


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
    parser.add_argument('--number-of-copies', '-n', type=int, default=10,
                        help='Number of copy sets to generate; placed in a '
                             'line into the empty half of the EAAD FIR bbox.')
    parser.add_argument('--distance-nm', '-d', type=float, default=30.0,
                        help='Spacing in NM between successive copies.')
    parser.add_argument('--fir-designator', default='EAAD',
                        help='FIR designator whose bounding rectangle is used '
                             'to choose the copy direction (default: EAAD).')
    parser.add_argument('--exc-airspace-types', nargs='*', default=[],
                        metavar='TYPE',
                        help='Airspace types to exclude from multiplication '
                             '(e.g. P CTA CTA_P). FIR and FIR_P are always excluded.')
    parser.add_argument('--exc-features', nargs='*', default=[],
                        metavar='DESIGNATOR',
                        help='Exclude features whose aixm:designator matches '
                             'any of the given values, regardless of feature type.')
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

    count = args.number_of_copies
    if count > MAX_AIRPORT_COPIES:
        print(f"ERROR: --number-of-copies={count} exceeds the maximum of "
              f"{MAX_AIRPORT_COPIES}.")
        print("The AirportHeliport designator scheme uses one letter per "
              "copy (A..Z), so at most 26 copy sets can be generated.")
        sys.exit(1)

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
    print(f"  Number of copies: {count}")
    print(f"  Distance: {args.distance_nm} NM")
    print(f"  FIR:      {args.fir_designator}")
    print(f"  Excluded airspace types: {', '.join(sorted(ase_types_exclude))}")
    if args.exc_features:
        print(f"  Excluded feature designators: {', '.join(sorted(args.exc_features))}")
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

    # Locate the FIR bounding rectangle and the source anchor (AirportHeliport ARP)
    fir_polygon = find_fir_polygon(root, args.fir_designator)
    if not fir_polygon:
        parser.error(
            f"FIR airspace with designator '{args.fir_designator}' not found "
            f"in the input file.")
    lats = [p[0] for p in fir_polygon]
    lons = [p[1] for p in fir_polygon]
    bbox = (min(lats), max(lats), min(lons), max(lons))

    anchor = find_anchor_position(root)
    if anchor is None:
        parser.error('No AirportHeliport ARP found in the input file to anchor '
                     'the copy direction.')
    anchor_lat, anchor_lon = anchor

    layout = compute_grid_layout(bbox, anchor_lat, anchor_lon, args.distance_nm)
    bbox_cols = layout['max_cols'] + 1
    bbox_rows = layout['max_rows'] + 1
    bbox_cells = bbox_cols * bbox_rows
    cols_per_row = choose_cols_per_row(count, layout)
    rows_used = (count + cols_per_row - 1) // cols_per_row
    row_dir = 'north' if layout['lat_sign'] > 0 else 'south'
    col_dir = 'east' if layout['lon_sign'] > 0 else 'west'

    print(f"  FIR bbox: lat [{bbox[0]:.4f}, {bbox[1]:.4f}], "
          f"lon [{bbox[2]:.4f}, {bbox[3]:.4f}]")
    print(f"  FIR centre: lat {(bbox[0]+bbox[1])/2:.4f}, "
          f"lon {(bbox[2]+bbox[3])/2:.4f}")
    print(f"  Anchor ARP: lat {anchor_lat:.4f}, lon {anchor_lon:.4f}  "
          f"(quarter {layout['quarter']})")
    print(f"  Grid grows {row_dir} (rows) and {col_dir} (cols); "
          f"using {rows_used} x {cols_per_row} cells "
          f"(bbox allows up to {bbox_rows} x {bbox_cols} = {bbox_cells})")
    if rows_used > bbox_rows:
        print(f"  WARNING: needed {rows_used} rows > {bbox_rows} that fit in "
              f"the FIR bounding rectangle; lower rows will fall outside.")
    print()

    # Extract all features by type
    print("Extracting features by type ...")
    features_by_type = extract_features_by_type(root)
    for ft in FEATURE_TYPES:
        print(f"  {ft}: {len(features_by_type[ft])} total in file")

    # Collect all features to clone
    collected, airport_membership = collect_eadd_features(
        features_by_type, ase_types_exclude)

    # Filter out features by designator if --exc-features specified
    exc_designators = set(args.exc_features)
    if exc_designators:
        excluded_feats = []
        for fuuid in list(collected):
            ftype, felem = collected[fuuid]
            desig = get_feature_designator(felem)
            if desig and desig in exc_designators:
                excluded_feats.append((ftype, desig))
                del collected[fuuid]
                airport_membership.pop(fuuid, None)
        if excluded_feats:
            print(f"  Excluded by --exc-features:")
            for ftype, desig in excluded_feats:
                print(f"    {ftype} designator={desig}")

    total_per_copy = len(collected)
    print(f"  TOTAL features per copy: {total_per_copy}")

    lat_mid = (bbox[0] + bbox[1]) / 2
    lon_mid = (bbox[2] + bbox[3]) / 2
    within_anchor_count = 0
    quadrant_counts = {}
    no_position_count = 0
    for fuuid, (ftype, felem) in collected.items():
        fpos = get_feature_position(felem)
        if fpos is None:
            no_position_count += 1
            continue
        dist = haversine_distance_nm(fpos[0], fpos[1], anchor_lat, anchor_lon)
        if dist <= 90.0:
            within_anchor_count += 1
        else:
            in_upper = fpos[0] >= lat_mid
            in_right = fpos[1] >= lon_mid
            qname = _quarter_name(in_upper, in_right)
            quadrant_counts[qname] = quadrant_counts.get(qname, 0) + 1
    print(f"\n  Per-feature offset direction (90 NM threshold from anchor):")
    print(f"    Follow anchor direction ({layout['quarter']}): {within_anchor_count}")
    for q, cnt in sorted(quadrant_counts.items()):
        print(f"    Own quadrant {q}: {cnt}")
    if no_position_count > 0:
        print(f"    No position detected (follow anchor): {no_position_count}")

    # Identify features that sit within BORDER_PROXIMITY_NM of the FIR
    # polygon edge.  Their copies (including copy 1) will be shifted
    # BORDER_SHIFT_NM inward along their own quadrant direction.
    # Check every geographic vertex, not just the representative point,
    # so large airspaces (e.g. EAV7, EAR5) whose first vertex sits far
    # from the border but whose boundary touches it are still flagged.
    border_near_uuids = set()
    border_near_info = []
    for fuuid, (ftype, felem) in collected.items():
        d = min_feature_distance_to_polygon_nm(felem, fir_polygon)
        if d < BORDER_PROXIMITY_NM:
            border_near_uuids.add(fuuid)
            border_near_info.append((ftype, get_feature_designator(felem), d))
    print(f"\n  Border-proximity shift "
          f"(< {BORDER_PROXIMITY_NM:.1f} NM from FIR polygon edge -> "
          f"+{BORDER_SHIFT_NM:.1f} NM inward on every copy): "
          f"{len(border_near_uuids)} feature(s)")
    for ftype, desig, dist in sorted(border_near_info, key=lambda x: x[2]):
        print(f"    {ftype} designator={desig}  (edge distance {dist:.2f} NM)")

    # Feature types that always go into Common/
    COMMON_ONLY_TYPES = {
        'VerticalStructure', 'Airspace', 'DesignatedPoint',
        'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon',
    }
    # Feature types that go into airport folders if they have airport membership,
    # otherwise into Common/
    AIRPORT_OR_COMMON_TYPES = {
        'AirportHeliport', 'Runway', 'RunwayDirection', 'RunwayElement',
        'RunwayCentrelinePoint', 'TouchDownLiftOff', 'Taxiway', 'TaxiwayElement',
        'Apron', 'ApronElement', 'AircraftStand',
    }

    # Generate copies
    print(f"\nGenerating {count} copies ({count * total_per_copy} features total) ...")
    all_cloned = []          # flat list of all (type, elem, uuid) across all copies
    per_copy_data = []       # list of (cloned, new_membership, airport_names)

    for i in range(count):
        copy_num = i + 1
        row = i // cols_per_row
        col = i % cols_per_row

        anchor_lat_off = row * layout['d_lat'] * layout['lat_sign']
        anchor_lon_off = col * layout['d_lon'] * layout['lon_sign']

        # Compute beginPosition for this copy set
        copy_begin = None
        if effective_start is not None:
            if time_offset is not None:
                copy_dt = effective_start + time_offset * i
            else:
                copy_dt = effective_start
            copy_begin = copy_dt.strftime('%Y-%m-%dT%H:%M:%SZ')

        time_info = f"  validTime.beginPosition={copy_begin}" if copy_begin else ""
        print(f"  Copy {copy_num:02d}:  grid (row {row}, col {col})  "
              f"anchor offset {anchor_lat_off:+.4f}° lat, {anchor_lon_off:+.4f}° lon{time_info}")

        cloned, new_membership, airport_names = clone_feature_set(
            collected, airport_membership, i,
            row, col, layout, bbox,
            anchor_lat, anchor_lon, 90.0,
            begin_position=copy_begin,
            border_near_uuids=border_near_uuids,
        )
        per_copy_data.append((cloned, new_membership, airport_names))
        all_cloned.extend(cloned)

    print_excluded_refs_summary()

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
