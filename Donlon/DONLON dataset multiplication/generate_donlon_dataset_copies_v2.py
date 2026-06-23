#!/usr/bin/env python3
r"""
====================================================================
Python script for iNM eEAD - Donlon TMA-area dataset copies (version 2)
Source: https://github.com/aixm/Donlon_2025/tree/main/Donlon
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

This script (version 2) multiplies the Donlon dataset features that lie IN or
NEAR the Donlon TMA, and lays the copies out on a regular 6 x 5 grid with equal
horizontal and vertical spacing, sized to fit inside the EAAD (AMSWELL) FIR
polygon.

Spatial selection
------------------
A feature is multiplied when it sits inside the Donlon TMA airspace OR within a
configurable radius (default 30 NM) of the TMA polygon edge:
  - point / areal features (Navaid, DesignatedPoint, VerticalStructure, AeronauticalGroundLight, Airspace) are tested by their own geometry
    (any geographic vertex inside the TMA, or within --radius-nm of its edge);
  - airport-related features (Runway, RunwayDirection, RunwayElement, RunwayCentrelinePoint, TouchDownLiftOff, Taxiway, TaxiwayElement, Apron,
    ApronElement, AircraftStand, WorkArea) follow their owning AirportHeliport: the whole airport sub-tree is kept iff the airport's ARP is in range
    (Runway/Taxiway/Apron carry no geometry of their own, only their child elements do, so they cannot be tested individually);
  - NavaidEquipment (VOR, DME, NDB, TACAN, Localizer, Glidepath, MarkerBeacon) follows its parent Navaid.

Multiplied feature types
------------------------
  - AirportHeliport and associated features
    - Runway, RunwayDirection, RunwayElement, RunwayCentrelinePoint, TouchDownLiftOff
    - Taxiway, TaxiwayElement
    - Apron, ApronElement, AircraftStand
    - WorkArea
  - VerticalStructure
  - Navaid and NavaidEquipment
  - DesignatedPoint
  - AeronauticalGroundLight
  - Airspace (except FIR, UIR, AWY, A and any --exc-airspace-types)

Layout strategy
---------------
The whole selected feature set is treated as one scene anchored at the Donlon TMA centroid.  The user picks --num-copies; the copies fill a fixed 6 x 5 grid
(30 cells) from the top-left (north-west) towards the right and down, the partial last row centred horizontally.  The grid uses a single ground pitch (NM) -
the largest that still fits the grid inside the EAAD FIR bounding box - so the spacing is the same horizontally and vertically; the grid block is centred in
the FIR bbox and any grid cell whose centre falls outside the (irregular) FIR polygon is pulled in toward the polygon centroid until it is inside.  Each copy
moves the scene so the TMA centroid lands on that cell's centre: latitude is offset, and longitude
is scaled about the anchor by cos(anchor_lat)/cos(target_lat) so the copy keeps the source's true ground shape (east-west width) at its new latitude instead of
being stretched in the north / squished in the south by meridian convergence.

Per copy the features are renamed / re-identified (new UUIDs, new airport designators E.D{A..}/E.H{A..}/..., -NN name suffixes, Airspace designatorICAO forced to NO, etc.)
and xlink:href references between copied features are remapped.  References to features that are NOT copied are left pointing at the original UUIDs.
The OrganisationAuthority features referenced this way (theOrganisationAuthority / specialDateAuthority) are emitted once, verbatim, into a shared
Donlon_OrganisationAuthority.xml at the top of the output folder, with their begin positions set to --effectiveDateStart, so those references resolve.

Run with no command-line arguments to be prompted for each input on its own line
(an empty answer or a single hyphen '-' leaves an optional field unset):
  python generate_donlon_dataset_copies_v2.py

Usage example:
python generate_donlon_dataset_copies_v2.py
Use hyphen '-' to leave an optional input empty.
input file location: "D:\...\Donlon_ALL_Baseline.xml"
output directory location (optional): -
number of copies (max 26): 26
inclusion radius around Donlon Intl. (default 40NM): 40
effective date start: 2026-06-27T00:00:00Z
temporality cases directory (optional): "D:\...\Donlon_dataset_multiplication"
apply ADM fix (yes/no): yes
new state uuid (optional): cd1b4070-79b3-4eb1-a496-b525d4e5a7c6
new caa uuid (optional): 2912da48-dad9-438c-b28b-3873effa4d17

Input parameters:
- input file location -> input AIXM XML file path
- output directory location -> (optional) output folder (default: Donlon_Dataset_Copies next to the script)
- number of copies -> number of copies (default 26, max 26); they fill a fixed 6 x 5 grid from the top-left towards the right and down, the partial last row centred; must be between 1 and 26 (one designator letter per copy)
- inclusion radius around Donlon Intl. -> selection radius around the TMA polygon edge (default 40 NM)
- effective date start -> (example: 2026-06-27T00:00:00Z) sets validTime.beginPosition of each feature to the specified date
- temporality cases directory -> (optional) folder of temporality use-case templates replicated into every Donlon_Copy_NN as Temporality_cases_NN; if not specified, no temporality cases are replicated
- apply ADM fix -> yes/no; when yes, apply the upper/lower limit (UNL/GND/FLOOR/CEILING + upper/lowerLimitReference) and Timesheet startDate/endDate corrections (same logic as create_donlon_all_baseline_ADM_fix.py, embedded so this script is standalone) to the source before copying AND to every replicated temporality use-case file, so the copies and their temporality cases inherit them (feature removal is not applied)
- new state uuid -> (optional) replace every reference to the Donlon State OrganisationAuthority (709c64da-44e4-47c7-9d57-326a04cbdd3c, "REPUBLIC OF DONLON EA STATE") with this UUID in all copies and their temporality cases
- new caa uuid -> (optional) replace every reference to the Donlon CAA OrganisationAuthority (c225ae5c-540f-4a48-8867-809b393b2407, "DONLON CIVIL AVIATION ADMINISTRATION EA-CAA") with this UUID in all copies and their temporality cases
"""

import argparse
import copy
import math
import os
import re
import sys
import uuid
from collections import defaultdict
from datetime import datetime
from lxml import etree

# Counter for xlink references intentionally not carried over to clones
# (replaced with xsi:nil).  Keyed by (feature_type, property_name).
EXCLUDED_REF_LOG = defaultdict(int)


def record_excluded_ref(feature_type, property_name, count=1):
    EXCLUDED_REF_LOG[(feature_type, property_name)] += count


def print_excluded_refs_summary():
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
GML_POS = '{http://www.opengis.net/gml/3.2}pos'
GML_POSLIST = '{http://www.opengis.net/gml/3.2}posList'

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
    'WorkArea',
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
    'AeronauticalGroundLight',
    'Airspace',
]

# Airspace types always excluded from copying
AIRSPACE_TYPES_EXCLUDE_DEFAULT = {'FIR', 'UIR', 'AWY', 'A'}

# Output ordering for the combined file
ALL_FEATURES_ORDER = [
    'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon',
    'DesignatedPoint',
    'AirportHeliport',
    'Airspace',
    'Taxiway', 'TaxiwayElement',
    'Apron', 'ApronElement', 'AircraftStand',
    'Runway', 'RunwayElement', 'RunwayDirection',
    'RunwayCentrelinePoint', 'TouchDownLiftOff',
    'WorkArea',
    'VerticalStructure',
    'AeronauticalGroundLight',
]

NAVAID_EQUIPMENT_TYPES = ['VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon']

VS_PROPERTIES_TO_REMOVE = [
    'hostedPassengerService',
    'supportedGroundLight',
    'hostedSpecialNavStation',
    'hostedUnit',
    'hostedOrganisation',
    'supportedService',
]

# AirportHeliport designator prefixes by name substring (case-insensitive).
AIRPORT_DESIGNATOR_PREFIX = [
    ('DONLON/DOWNTOWN HELIPORT', 'EAH'),
    ('DONLON/INTL',              'EAD'),
    ('MAGNETO',                  'EAM'),
    ('AKVIN',                    'EAK'),
]
MAX_AIRPORT_COPIES = 26  # A..Z

# Fraction of the EAAD FIR bbox kept clear (inset) at each edge before the grid
# is laid out, so copies don't hug the FIR boundary.
MARGIN_FRAC = 0.10

# Fixed grid frame the copies are laid out on.  The user specifies how many
# copies to make; they fill this frame row by row from the top-left (north-west)
# towards the right and down.  row 0 = north, col 0 = west.  A partial last row
# is centred horizontally with even spacing.
GRID_ROWS = 6
GRID_COLS = 5


def get_airport_designator_prefix(name):
    if not name:
        return None
    up = name.upper()
    for key, prefix in AIRPORT_DESIGNATOR_PREFIX:
        if key in up:
            return prefix
    return None


# ---------------------------------------------------------------------------
# Geometry helpers
# ---------------------------------------------------------------------------


def generate_new_uuid():
    return str(uuid.uuid4())


def haversine_distance_nm(lat1, lon1, lat2, lon2):
    """Great-circle distance in nautical miles between two points (degrees)."""
    R_nm = 3440.065
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlam = math.radians(lon2 - lon1)
    a = (math.sin(dphi / 2) ** 2
         + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2)
    return 2 * R_nm * math.asin(math.sqrt(a))


def point_in_polygon(lat, lon, polygon):
    """Ray-casting point-in-polygon test.  polygon is a list of (lat, lon)."""
    inside = False
    n = len(polygon)
    if n < 3:
        return False
    j = n - 1
    for i in range(n):
        lati, loni = polygon[i]
        latj, lonj = polygon[j]
        if (loni > lon) != (lonj > lon):
            denom = (lonj - loni)
            if denom != 0 and lat < (latj - lati) * (lon - loni) / denom + lati:
                inside = not inside
        j = i
    return inside


def _point_to_segment_distance_nm(plat, plon, lat1, lon1, lat2, lon2):
    """Approx. distance (NM) from a point to a segment via an equirectangular
    projection centred on the point.  Adequate for short distances."""
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
    return math.hypot(x1 + t * dx, y1 + t * dy)


def distance_to_polygon_nm(plat, plon, polygon):
    """Distance (NM) from a point to a closed polygon: 0 if inside, else the
    minimum perpendicular distance to any edge."""
    if not polygon or len(polygon) < 2:
        return float('inf')
    if point_in_polygon(plat, plon, polygon):
        return 0.0
    min_d = float('inf')
    n = len(polygon)
    for i in range(n):
        lat1, lon1 = polygon[i]
        lat2, lon2 = polygon[(i + 1) % n]
        d = _point_to_segment_distance_nm(plat, plon, lat1, lon1, lat2, lon2)
        if d < min_d:
            min_d = d
    return min_d


def iter_feature_geographic_vertices(feature_elem):
    """Yield (lat, lon) for every EPSG:4326 vertex carried directly by a
    feature.  Projected (EPSG:3395 metres) and out-of-range values are skipped."""
    for pos in feature_elem.iter(GML_POS):
        if pos.text and pos.text.strip():
            parts = pos.text.strip().split()
            if len(parts) >= 2:
                try:
                    lat, lon = float(parts[0]), float(parts[1])
                except ValueError:
                    continue
                if -90 <= lat <= 90 and -180 <= lon <= 180:
                    yield lat, lon
    for pos_list in feature_elem.iter(GML_POSLIST):
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
    """Smallest distance (NM) from any of a feature's geographic vertices to the
    polygon (0 if any vertex is inside).  +inf if the feature has no geographic
    coordinate of its own."""
    min_d = float('inf')
    for lat, lon in iter_feature_geographic_vertices(feature_elem):
        d = distance_to_polygon_nm(lat, lon, polygon)
        if d < min_d:
            min_d = d
            if min_d == 0.0:
                break
    return min_d


def get_feature_position(feature_elem):
    """Representative (lat, lon) of a feature: its first geographic vertex."""
    for lat, lon in iter_feature_geographic_vertices(feature_elem):
        return lat, lon
    return None


def polygon_bbox(polygon):
    lats = [p[0] for p in polygon]
    lons = [p[1] for p in polygon]
    return min(lats), max(lats), min(lons), max(lons)


def polygon_centroid(polygon):
    lats = [p[0] for p in polygon]
    lons = [p[1] for p in polygon]
    return sum(lats) / len(lats), sum(lons) / len(lons)


# ---------------------------------------------------------------------------
# TMA / FIR lookup
# ---------------------------------------------------------------------------

# The selection always anchors on the Donlon TMA airspace and distributes the
# copies inside the EAAD (AMSWELL) FIR.  Both are identified by their fixed
# baseline UUIDs.
DONLON_TMA_UUID = '9eaf01db-0eff-415d-a6db-fbdfc145b2b8'
DONLON_FIR_UUID = 'f4d5e4d4-d84a-481f-b9e3-b359e42c0dff'

# OrganisationAuthority features that are referenced (theOrganisationAuthority /
# specialDateAuthority / ...) throughout the baseline but are NOT among the
# OrganisationAuthority features emitted into Donlon_OrganisationAuthority.xml -
# they are external authorities.  The optional --state-uuid / --caa-uuid CLI
# options let the user replace every reference to these two UUIDs with their own,
# so the copies (and their temporality cases) point at the user's State / CAA
# OrganisationAuthority instead.
DONLON_STATE_OA_UUID = '709c64da-44e4-47c7-9d57-326a04cbdd3c'  # REPUBLIC OF DONLON EA STATE
DONLON_CAA_OA_UUID = 'c225ae5c-540f-4a48-8867-809b393b2407'   # DONLON CIVIL AVIATION ADMINISTRATION EA-CAA

# Features whose recorded location lies outside the TMA selection but which must
# still be copied into every clone.  Their gml:pos is overridden (in the source,
# before selection) to the coordinates below "lat lon", so they are treated as if
# located there: they then fall inside the selection and are cloned and
# translated rigidly with the rest of the scene.
POSITION_OVERRIDES = {
    # AeronauticalGroundLight ATURA (BCN) -> inside the TMA area
    '9481f274-f05b-4c00-9017-eae75d33c45b': (53.00298026, -32.83127779),
    # AeronauticalGroundLight SIBY (AWY_BCN) -> inside the TMA area
    'a552aba9-aed1-452f-a50e-347281817f96': (51.85598895, -32.41100662),
    # Navaid NDB RIC RICHMAAST -> inside the TMA area
    '75b83517-5580-4e04-8818-89f00d751482': (52.84266701, -31.34571581),
    # NDB RIC RICHMAAST (NavaidEquipment of the Navaid above) -> same position
    '95418061-d8a1-4872-b04e-6e741a59bcd0': (52.84266701, -31.34571581),
    # Airspace EAV11 ULENI (HANG GLIDING AREA) circle centre -> inside the TMA area
    'd9bde2f0-a97f-40d5-83f4-de5c711473ab': (51.67928152, -32.58698181),
    # Airspace EAV10 TOMAR circle centre -> inside the TMA area
    'df7b7fab-5508-44c3-802b-46cbafc75091': (53.17573707, -32.61630306),
    # Navaid NDB WNR WICHNOR/SLIPTON -> inside the TMA area
    '8e650273-7861-4066-b6ef-696d2f71dcda': (51.56368878, -31.62426763),
    # NDB WNR WICHNOR/SLIPTON (NavaidEquipment of the Navaid above) -> same position
    'e978e242-02ab-456d-8497-85e79af1a533': (51.56368878, -31.62426763),
}

GML_IDENTIFIER = '{http://www.opengis.net/gml/3.2}identifier'
AIXM_NAME = '{http://www.aixm.aero/schema/5.1.1}name'
AIXM_NS = '{http://www.aixm.aero/schema/5.1.1}'

# Temporality use-case templates.  The whole folder is replicated into every
# Donlon_Copy_NN/ as Temporality_cases_NN/, each file with the referenced
# feature's identity (gml:id/gml:identifier), xlink:href references, name and
# designator remapped to the per-copy clone, the seq=1 begin positions synced to
# the per-copy clone, and the geometry moved to the copy's position with the same
# latitude-offset + longitude-scale transform the clone received.
TEMPORALITY_CASES_DIRNAME = 'EAD-SDD_temporality_cases'
# Per-copy output folder name (kept short to stay under the Windows 260-char path
# limit).  The copy number is appended: e.g. Temporality_cases_01.
TEMPORALITY_OUTPUT_DIRNAME = 'Temporality_cases'
# Files whose feature is newly commissioned (does NOT exist in the baseline): it
# gets a fresh random gml:identifier, its xlink:href references are still
# remapped, and its begin positions are set to the copy set's start time.
TEMPORALITY_NEW_FEATURE_FILES = {'Commissioning_of_a_Feature.xml'}
# Baseline initial start date used throughout the temporality templates; it is
# find/replaced with each copy's start date in the generated temporality files.
TEMPORALITY_BASELINE_START = '2025-11-01T00:00:00Z'


def apply_position_overrides(root):
    """Override the gml:pos of the POSITION_OVERRIDES features (matched by
    gml:identifier UUID) so they are treated as if located at the given
    coordinates for both spatial selection and cloning.  Returns a list of
    (uuid, name, old_pos, new_pos) tuples for reporting."""
    found = {}
    for ident in root.iter(GML_IDENTIFIER):
        if ident.text and ident.text.strip() in POSITION_OVERRIDES:
            found[ident.text.strip()] = ident.getparent()
    applied = []
    for fuuid, (lat, lon) in POSITION_OVERRIDES.items():
        feat = found.get(fuuid)
        if feat is None:
            print(f"  WARNING: position-override feature {fuuid} not found in input.")
            continue
        new_pos = f"{lat} {lon}"
        positions = list(feat.iter(GML_POS))
        old_pos = positions[0].text.strip() if positions and positions[0].text else None
        for pos in positions:
            pos.text = new_pos
        name = feat.findtext(f'.//{AIXM_NAME}')
        applied.append((fuuid, name, old_pos, new_pos))
    return applied


def find_airspace_polygon_by_uuid(root, feature_uuid):
    """Return the exterior polygon (list of (lat, lon)) of the Airspace whose
    gml:identifier equals feature_uuid, or None."""
    for member in root.findall('message:hasMember', NSMAP):
        airspace = member.find('aixm:Airspace', NSMAP)
        if airspace is None or get_feature_uuid(airspace) != feature_uuid:
            continue
        for pos_list in airspace.iter(GML_POSLIST):
            if not pos_list.text:
                continue
            values = pos_list.text.strip().split()
            polygon = []
            for i in range(0, len(values) - 1, 2):
                try:
                    polygon.append((float(values[i]), float(values[i + 1])))
                except ValueError:
                    pass
            if polygon:
                return polygon
        return None
    return None


# ---------------------------------------------------------------------------
# Grid distribution inside the EAAD FIR
# ---------------------------------------------------------------------------


def _pull_inside(lat, lon, polygon, clat, clon):
    """If (lat, lon) is outside the polygon, step it toward the centroid
    (clat, clon) until it falls inside.  Returns the adjusted (lat, lon)."""
    if point_in_polygon(lat, lon, polygon):
        return lat, lon, False
    for t in (0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95):
        nlat = lat + (clat - lat) * t
        nlon = lon + (clon - lon) * t
        if point_in_polygon(nlat, nlon, polygon):
            return nlat, nlon, True
    return clat, clon, True


def build_fir_grid(polygon, rows, cols, num_copies, margin_frac=0.10):
    """Place `num_copies` points on a fixed rows x cols frame inside the EAAD
    FIR bbox (inset by margin_frac on each side) with the SAME ground spacing
    (NM) horizontally and vertically.

    A single ground pitch (NM) is used in both directions - the largest that
    still fits the rows x cols block inside the inset bbox.  Each row's longitude
    step is derived from that pitch with a cos(row_lat) correction, so the
    east-west ground distance between neighbours equals the north-south distance
    at every latitude (instead of being stretched north / squished south).  The
    block is centred in the inset bbox and filled row by row from the top-left
    (row 0 = north, col 0 = west) towards the right and down; the last (partial)
    row is centred horizontally.  Any point that lands outside the polygon is
    pulled inward toward the centroid.

    Returns a list of dicts {'row', 'col', 'index', 'lat', 'lon', 'pulled'} in
    fill order (index = 0 .. num_copies-1).
    """
    min_lat, max_lat, min_lon, max_lon = polygon_bbox(polygon)
    clat, clon = polygon_centroid(polygon)

    # Symmetric inset so copies don't hug the FIR boundary.
    dlat = max_lat - min_lat
    dlon = max_lon - min_lon
    min_lat += dlat * margin_frac
    max_lat -= dlat * margin_frac
    min_lon += dlon * margin_frac
    max_lon -= dlon * margin_frac

    center_lon = (min_lon + max_lon) / 2.0

    # Available ground extents (NM) of the inset bbox.  For the east-west extent
    # use cos(max_lat) - the smallest cosine, i.e. the row that needs the most
    # longitude degrees - so the chosen pitch fits every row inside the bbox.
    gaps_v = max(rows - 1, 1)
    gaps_h = max(cols - 1, 1)
    avail_h_nm = (max_lat - min_lat) * 60.0
    cos_widest = math.cos(math.radians(max_lat))
    avail_w_nm = (max_lon - min_lon) * 60.0 * (cos_widest if cos_widest > 1e-6 else 1.0)

    # One ground pitch (NM) used in both directions.
    pitch_nm = min(avail_h_nm / gaps_v, avail_w_nm / gaps_h)
    pitch_lat_deg = pitch_nm / 60.0

    # Centre the grid block vertically in the inset bbox.
    grid_h_deg = pitch_lat_deg * gaps_v
    top_lat = max_lat - ((max_lat - min_lat) - grid_h_deg) / 2.0

    cells = []
    for i in range(num_copies):
        r = i // cols
        c = i % cols
        # Copies in this row (the last row may be partial); centre a partial row
        # by shifting its columns right by (cols - row_count) / 2.
        row_count = min(cols, num_copies - r * cols)
        col_pos = c + (cols - row_count) / 2.0

        lat = top_lat - pitch_lat_deg * r  # row 0 = north

        # Per-row longitude step so the east-west ground spacing equals pitch_nm
        # at this latitude; each row is centred on the bbox centre longitude.
        cos_r = math.cos(math.radians(lat))
        pitch_lon_deg = pitch_nm / (60.0 * cos_r) if cos_r > 1e-6 else pitch_nm / 60.0
        left_lon = center_lon - pitch_lon_deg * gaps_h / 2.0
        lon = left_lon + pitch_lon_deg * col_pos  # col 0 = west

        adj_lat, adj_lon, pulled = _pull_inside(lat, lon, polygon, clat, clon)
        cells.append({
            'row': r, 'col': c, 'index': i,
            'lat': adj_lat, 'lon': adj_lon, 'pulled': pulled,
        })
    return cells


# ---------------------------------------------------------------------------
# Feature extraction
# ---------------------------------------------------------------------------


def get_feature_uuid(feature_elem):
    ident = feature_elem.find('gml:identifier', NSMAP)
    return ident.text.strip() if ident is not None and ident.text else None


def get_ref_uuid(feature_elem, ref_element_name):
    """UUID referenced by aixm:<ref_element_name> inside the feature's
    TimeSlice, or None."""
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
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            d = child.find('aixm:designator', NSMAP)
            if d is not None and d.text:
                return d.text.strip()
            break
    return None


def get_airport_name(feature_elem):
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'AirportHeliportTimeSlice' in tag:
            n = child.find('aixm:name', NSMAP)
            if n is not None and n.text:
                return n.text
            break
    return None


def get_feature_name(feature_elem):
    """Return the aixm:name text from the feature's first TimeSlice, or None.
    Returns the raw text (not stripped) since names can contain spaces."""
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            n = child.find('aixm:name', NSMAP)
            if n is not None and n.text:
                return n.text
            return None
    return None


def get_feature_begin_positions(feature_elem):
    """Return (validTime_begin, featureLifetime_begin) text from the feature's
    first TimeSlice; each element is None if absent."""
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            vt = child.find('gml:validTime/gml:TimePeriod/gml:beginPosition', NSMAP)
            fl = child.find('aixm:featureLifetime/gml:TimePeriod/gml:beginPosition', NSMAP)
            return (vt.text if vt is not None else None,
                    fl.text if fl is not None else None)
    return None, None


def get_airspace_type(feature_elem):
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'AirspaceTimeSlice' in tag:
            t = child.find('aixm:type', NSMAP)
            if t is not None and t.text:
                return t.text.strip()
            break
    return None


def extract_features_by_type(root):
    """{ type_name: { uuid: element } }."""
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


def collect_features(features_by_type, ase_types_exclude=None):
    """
    Collect every candidate feature and the membership maps used by the spatial
    filter.

    Returns:
        collected: { uuid: (type_name, element) }
        airport_membership: { feature_uuid: airport_uuid }
        navaid_equipment: { navaid_uuid: set(equipment_uuid) }
    """
    collected = {}
    airport_membership = {}

    for fuuid, felem in features_by_type['AirportHeliport'].items():
        collected[fuuid] = ('AirportHeliport', felem)
        airport_membership[fuuid] = fuuid

    runway_to_airport = {}
    for fuuid, felem in features_by_type['Runway'].items():
        collected[fuuid] = ('Runway', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            runway_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    rwydir_to_runway = {}
    for fuuid, felem in features_by_type['RunwayDirection'].items():
        collected[fuuid] = ('RunwayDirection', felem)
        rwy_uuid = get_ref_uuid(felem, 'usedRunway')
        if rwy_uuid:
            rwydir_to_runway[fuuid] = rwy_uuid
            ahp_uuid = runway_to_airport.get(rwy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    for fuuid, felem in features_by_type['RunwayElement'].items():
        collected[fuuid] = ('RunwayElement', felem)
        rwy_uuid = get_ref_uuid(felem, 'associatedRunway')
        if rwy_uuid:
            ahp_uuid = runway_to_airport.get(rwy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    for fuuid, felem in features_by_type['RunwayCentrelinePoint'].items():
        collected[fuuid] = ('RunwayCentrelinePoint', felem)
        rwydir_uuid = get_ref_uuid(felem, 'onRunway')
        if rwydir_uuid:
            rwy_uuid = rwydir_to_runway.get(rwydir_uuid)
            if rwy_uuid:
                ahp_uuid = runway_to_airport.get(rwy_uuid)
                if ahp_uuid:
                    airport_membership[fuuid] = ahp_uuid

    tdlof_to_airport = {}
    for fuuid, felem in features_by_type['TouchDownLiftOff'].items():
        collected[fuuid] = ('TouchDownLiftOff', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            tdlof_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    taxiway_to_airport = {}
    for fuuid, felem in features_by_type['Taxiway'].items():
        collected[fuuid] = ('Taxiway', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            taxiway_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    for fuuid, felem in features_by_type['TaxiwayElement'].items():
        collected[fuuid] = ('TaxiwayElement', felem)
        twy_uuid = get_ref_uuid(felem, 'associatedTaxiway')
        if twy_uuid:
            ahp_uuid = taxiway_to_airport.get(twy_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    apron_to_airport = {}
    for fuuid, felem in features_by_type['Apron'].items():
        collected[fuuid] = ('Apron', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            apron_to_airport[fuuid] = ahp_uuid
            airport_membership[fuuid] = ahp_uuid

    apronelem_to_apron = {}
    for fuuid, felem in features_by_type['ApronElement'].items():
        collected[fuuid] = ('ApronElement', felem)
        apron_uuid = get_ref_uuid(felem, 'associatedApron')
        if apron_uuid:
            apronelem_to_apron[fuuid] = apron_uuid
            ahp_uuid = apron_to_airport.get(apron_uuid)
            if ahp_uuid:
                airport_membership[fuuid] = ahp_uuid

    for fuuid, felem in features_by_type['AircraftStand'].items():
        collected[fuuid] = ('AircraftStand', felem)
        ae_uuid = get_ref_uuid(felem, 'apronLocation')
        if ae_uuid:
            apron_uuid = apronelem_to_apron.get(ae_uuid)
            if apron_uuid:
                ahp_uuid = apron_to_airport.get(apron_uuid)
                if ahp_uuid:
                    airport_membership[fuuid] = ahp_uuid

    for fuuid, felem in features_by_type['WorkArea'].items():
        collected[fuuid] = ('WorkArea', felem)
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            airport_membership[fuuid] = ahp_uuid

    # Navaids + their equipment references
    for fuuid, felem in features_by_type['TouchDownLiftOff'].items():
        ahp_uuid = get_ref_uuid(felem, 'associatedAirportHeliport')
        if ahp_uuid:
            tdlof_to_airport[fuuid] = ahp_uuid

    navaid_equipment = {}
    for fuuid, felem in features_by_type['Navaid'].items():
        if fuuid not in collected:
            collected[fuuid] = ('Navaid', felem)
        ahp_uuid = get_ref_uuid(felem, 'servedAirport')
        if not ahp_uuid:
            rwydir_uuid = get_ref_uuid(felem, 'runwayDirection')
            if rwydir_uuid:
                rwy_uuid = rwydir_to_runway.get(rwydir_uuid)
                if rwy_uuid:
                    ahp_uuid = runway_to_airport.get(rwy_uuid)
        if not ahp_uuid:
            tdlof_uuid = get_ref_uuid(felem, 'touchDownLiftOff')
            if tdlof_uuid:
                ahp_uuid = tdlof_to_airport.get(tdlof_uuid)
        if ahp_uuid:
            airport_membership[fuuid] = ahp_uuid
        eq_uuids = set()
        for eq_ref in felem.iter('{http://www.aixm.aero/schema/5.1.1}theNavaidEquipment'):
            href = eq_ref.get(XLINK_HREF)
            if href and href.startswith('urn:uuid:'):
                eq_uuids.add(href.replace('urn:uuid:', ''))
        navaid_equipment[fuuid] = eq_uuids

    for eq_type in NAVAID_EQUIPMENT_TYPES:
        for fuuid, felem in features_by_type[eq_type].items():
            if fuuid not in collected:
                collected[fuuid] = (eq_type, felem)

    for fuuid, felem in features_by_type['DesignatedPoint'].items():
        if fuuid not in collected:
            collected[fuuid] = ('DesignatedPoint', felem)

    for fuuid, felem in features_by_type['VerticalStructure'].items():
        if fuuid not in collected:
            collected[fuuid] = ('VerticalStructure', felem)

    for fuuid, felem in features_by_type['AeronauticalGroundLight'].items():
        if fuuid not in collected:
            collected[fuuid] = ('AeronauticalGroundLight', felem)

    if ase_types_exclude is None:
        ase_types_exclude = AIRSPACE_TYPES_EXCLUDE_DEFAULT
    for fuuid, felem in features_by_type['Airspace'].items():
        if fuuid in collected:
            continue
        atype = get_airspace_type(felem)
        if atype is not None and atype in ase_types_exclude:
            continue
        collected[fuuid] = ('Airspace', felem)

    return collected, airport_membership, navaid_equipment


def spatial_filter(collected, airport_membership, navaid_equipment,
                   tma_polygon, radius_nm):
    """
    Keep only the features in/near the TMA.

      - AirportHeliport: kept iff its ARP is within radius_nm of the TMA.
      - Any airport-related feature: kept iff its owning airport is kept
        (so Runway/Taxiway/Apron, which carry no geometry of their own, follow
        the airport rather than being dropped).
      - Navaid: kept iff its own geometry is within range OR its airport is kept.
      - NavaidEquipment: kept iff its parent Navaid is kept.
      - DesignatedPoint / VerticalStructure / AeronauticalGroundLight / Airspace:
        kept iff their own geometry is within range.

    Returns (kept, dropped_no_geometry) where kept is a new
    { uuid: (type, elem) } dict and dropped_no_geometry lists
    (type, designator) of standalone features skipped for lack of geometry.
    """
    # Distance of each feature's own geometry to the TMA.
    own_dist = {}
    for fuuid, (ftype, felem) in collected.items():
        own_dist[fuuid] = min_feature_distance_to_polygon_nm(felem, tma_polygon)

    # 1. Airports in range (ARP always present).
    airports_in = set()
    for fuuid, (ftype, felem) in collected.items():
        if ftype == 'AirportHeliport' and own_dist[fuuid] <= radius_nm:
            airports_in.add(fuuid)

    # 2. Navaids in range (own geometry, or airport-related to a kept airport).
    navaids_in = set()
    for fuuid, (ftype, felem) in collected.items():
        if ftype != 'Navaid':
            continue
        if own_dist[fuuid] <= radius_nm or airport_membership.get(fuuid) in airports_in:
            navaids_in.add(fuuid)

    equipment_in = set()
    for nav_uuid in navaids_in:
        equipment_in |= navaid_equipment.get(nav_uuid, set())

    STANDALONE = {'DesignatedPoint', 'VerticalStructure', 'AeronauticalGroundLight'}

    kept = {}
    dropped_no_geometry = []
    for fuuid, (ftype, felem) in collected.items():
        keep = False
        if ftype == 'AirportHeliport':
            keep = fuuid in airports_in
        elif ftype == 'Navaid':
            keep = fuuid in navaids_in
        elif ftype in NAVAID_EQUIPMENT_TYPES:
            keep = fuuid in equipment_in
        elif fuuid in airport_membership:
            keep = airport_membership[fuuid] in airports_in
        elif ftype in STANDALONE:
            keep = own_dist[fuuid] <= radius_nm
        elif ftype == 'Airspace':
            if own_dist[fuuid] == float('inf'):
                dropped_no_geometry.append((ftype, get_feature_designator(felem)))
                keep = False
            else:
                keep = own_dist[fuuid] <= radius_nm
        if keep:
            kept[fuuid] = (ftype, felem)
    return kept, dropped_no_geometry


# ---------------------------------------------------------------------------
# Feature cloning
# ---------------------------------------------------------------------------


def update_feature_ids(feature_elem, new_uuid):
    feature_elem.set(GML_ID, f'uuid.{new_uuid}')
    ident = feature_elem.find('gml:identifier', NSMAP)
    if ident is not None:
        ident.text = new_uuid

    timeslice = None
    for child in feature_elem.iter():
        tag = child.tag
        if isinstance(tag, str) and 'TimeSlice' in tag and child is not feature_elem:
            timeslice = child
            break
    if timeslice is None:
        return

    seq_elem = timeslice.find('aixm:sequenceNumber', NSMAP)
    corr_elem = timeslice.find('aixm:correctionNumber', NSMAP)
    seq = int(seq_elem.text) if seq_elem is not None and seq_elem.text else 1
    corr = int(corr_elem.text) if corr_elem is not None and corr_elem.text else 0

    timeslice.set(GML_ID, f'id_{new_uuid}_{seq}_{corr}_B')

    child_idx = 1
    for elem in timeslice.iter():
        if elem is timeslice:
            continue
        if elem.get(GML_ID) is not None:
            elem.set(GML_ID, f'id_{new_uuid}_{seq}_{corr}_B_{child_idx}')
            child_idx += 1


def update_xlink_refs(feature_elem, uuid_map):
    for elem in feature_elem.iter():
        href = elem.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            old_uuid = href.replace('urn:uuid:', '')
            if old_uuid in uuid_map:
                elem.set(XLINK_HREF, f'urn:uuid:{uuid_map[old_uuid]}')


def replace_uuid_everywhere(elem, uuid_map):
    """Replace every occurrence of an OLD UUID with its NEW UUID anywhere in the
    given element subtree, for each OLD -> NEW pair in uuid_map:

      - xlink:href="urn:uuid:OLD"  -> "urn:uuid:NEW"
      - gml:id="uuid.OLD"          -> "uuid.NEW"
      - gml:identifier text OLD    -> NEW

    Used to point the Donlon State / CAA OrganisationAuthority references (which
    are not copied, only referenced) at user-supplied UUIDs.  Returns the number
    of substitutions made."""
    if not uuid_map:
        return 0
    n = 0
    for node in elem.iter():
        href = node.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            old = href[len('urn:uuid:'):]
            new = uuid_map.get(old)
            if new is not None:
                node.set(XLINK_HREF, f'urn:uuid:{new}')
                n += 1
        gid = node.get(GML_ID)
        if gid and gid.startswith('uuid.'):
            new = uuid_map.get(gid[len('uuid.'):])
            if new is not None:
                node.set(GML_ID, f'uuid.{new}')
                n += 1
        if node.tag == GML_IDENTIFIER and node.text:
            new = uuid_map.get(node.text.strip())
            if new is not None:
                node.text = new
                n += 1
    return n


def update_valid_time(feature_elem, new_begin_position):
    for ts in feature_elem.iter():
        tag = ts.tag
        if not (isinstance(tag, str) and 'TimeSlice' in tag):
            continue
        for bp in ts.iter('{http://www.opengis.net/gml/3.2}beginPosition'):
            bp.text = new_begin_position


# -- coordinate offsetting (EPSG:4326 + EPSG:3395 World Mercator) -----------

_MERCATOR_A = 6378137.0
_MERCATOR_E = 0.0818191908426


def _mercator_forward_y(lat_deg):
    phi = math.radians(lat_deg)
    sin_phi = math.sin(phi)
    return _MERCATOR_A * math.log(
        math.tan(math.pi / 4 + phi / 2)
        * ((1 - _MERCATOR_E * sin_phi) / (1 + _MERCATOR_E * sin_phi)) ** (_MERCATOR_E / 2)
    )


def _mercator_inverse_y(y):
    t = math.exp(-y / _MERCATOR_A)
    phi = math.pi / 2 - 2 * math.atan(t)
    for _ in range(15):
        sin_phi = math.sin(phi)
        phi_new = math.pi / 2 - 2 * math.atan(
            t * ((1 - _MERCATOR_E * sin_phi) / (1 + _MERCATOR_E * sin_phi)) ** (_MERCATOR_E / 2)
        )
        if abs(phi_new - phi) < 1e-14:
            break
        phi = phi_new
    return math.degrees(phi)


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
    return _wrap_pairs(coord_pairs, max_line_length)


def offset_mercator_pos_list(pos_list_str, lat_offset, lon_offset, max_line_length=200):
    values = pos_list_str.strip().split()
    delta_x = _MERCATOR_A * math.radians(lon_offset)
    coord_pairs = []
    for i in range(0, len(values), 2):
        if i + 1 < len(values):
            try:
                x = float(values[i])
                y = float(values[i + 1])
                lat = _mercator_inverse_y(y)
                new_y = _mercator_forward_y(lat + lat_offset)
                new_x = x + delta_x
                coord_pairs.append(f"{new_x:.2f} {new_y:.2f}")
            except ValueError:
                coord_pairs.append(f"{values[i]} {values[i + 1]}")
    return _wrap_pairs(coord_pairs, max_line_length)


def _wrap_pairs(coord_pairs, max_line_length):
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


def _find_ancestor_srs(parent_map, elem):
    node = elem
    while node is not None:
        srs = node.get('srsName')
        if srs:
            return srs
        node = parent_map.get(node)
    return None


def offset_all_coordinates(feature_elem, lat_offset, lon_offset):
    parent_map = {child: parent for parent in feature_elem.iter() for child in parent}
    for pos in feature_elem.iter(GML_POS):
        if pos.text and pos.text.strip():
            pos.text = offset_coordinate(pos.text, lat_offset, lon_offset)
    for pos_list in feature_elem.iter(GML_POSLIST):
        if not (pos_list.text and pos_list.text.strip()):
            continue
        srs = _find_ancestor_srs(parent_map, pos_list)
        if srs and 'EPSG::3395' in srs:
            pos_list.text = offset_mercator_pos_list(pos_list.text, lat_offset, lon_offset)
        else:
            pos_list.text = offset_pos_list(pos_list.text, lat_offset, lon_offset)


# -- latitude-offset + longitude-scale transform ----------------------------
# Placing a copy at a different latitude with a plain degree translation would
# distort its east-west ground width, because 1 deg of longitude = 60*cos(lat)
# NM (meridian convergence): the same degree-width covers less ground the
# farther north it sits, so northern copies look stretched and southern copies
# squished.  To keep every copy's true ground shape identical to the source we
# offset the latitude as before but *scale the longitude about the anchor* by
# cos(anchor_lat)/cos(target_lat):
#     lat' = lat + (target_lat - anchor_lat)
#     lon' = target_lon + (lon - anchor_lon) * lon_scale
# so the copy's east-west ground width (lon-extent * cos(target_lat)) equals the
# source's east-west ground width (lon-extent * cos(anchor_lat)).


def transform_coordinate(coord_str, anchor_lon, target_lon, lat_offset, lon_scale):
    parts = coord_str.strip().split()
    if len(parts) >= 2:
        try:
            lat = float(parts[0]) + lat_offset
            lon = target_lon + (float(parts[1]) - anchor_lon) * lon_scale
            return f"{lat} {lon}"
        except ValueError:
            pass
    return coord_str


def transform_pos_list(pos_list_str, anchor_lon, target_lon, lat_offset, lon_scale,
                       max_line_length=200):
    values = pos_list_str.strip().split()
    coord_pairs = []
    for i in range(0, len(values), 2):
        if i + 1 < len(values):
            try:
                lat = float(values[i]) + lat_offset
                lon = target_lon + (float(values[i + 1]) - anchor_lon) * lon_scale
                coord_pairs.append(f"{lat} {lon}")
            except ValueError:
                coord_pairs.append(f"{values[i]} {values[i + 1]}")
    return _wrap_pairs(coord_pairs, max_line_length)


def transform_mercator_pos_list(pos_list_str, anchor_lon, target_lon, lat_offset,
                                lon_scale, max_line_length=200):
    values = pos_list_str.strip().split()
    coord_pairs = []
    for i in range(0, len(values), 2):
        if i + 1 < len(values):
            try:
                x = float(values[i])
                y = float(values[i + 1])
                lat = _mercator_inverse_y(y)
                lon = math.degrees(x / _MERCATOR_A)
                new_y = _mercator_forward_y(lat + lat_offset)
                new_lon = target_lon + (lon - anchor_lon) * lon_scale
                new_x = _MERCATOR_A * math.radians(new_lon)
                coord_pairs.append(f"{new_x:.2f} {new_y:.2f}")
            except ValueError:
                coord_pairs.append(f"{values[i]} {values[i + 1]}")
    return _wrap_pairs(coord_pairs, max_line_length)


def transform_all_coordinates(feature_elem, anchor_lon, target_lon, lat_offset, lon_scale):
    """Offset latitude and scale longitude about the anchor (see note above)."""
    parent_map = {child: parent for parent in feature_elem.iter() for child in parent}
    for pos in feature_elem.iter(GML_POS):
        if pos.text and pos.text.strip():
            pos.text = transform_coordinate(
                pos.text, anchor_lon, target_lon, lat_offset, lon_scale)
    for pos_list in feature_elem.iter(GML_POSLIST):
        if not (pos_list.text and pos_list.text.strip()):
            continue
        srs = _find_ancestor_srs(parent_map, pos_list)
        if srs and 'EPSG::3395' in srs:
            pos_list.text = transform_mercator_pos_list(
                pos_list.text, anchor_lon, target_lon, lat_offset, lon_scale)
        else:
            pos_list.text = transform_pos_list(
                pos_list.text, anchor_lon, target_lon, lat_offset, lon_scale)


def clone_feature_set(collected_features, airport_membership, index,
                      anchor_lat, anchor_lon, target_lat, target_lon,
                      begin_position=None):
    """
    Clone the whole selected feature set for one copy, moving the scene from the
    anchor (TMA centroid) to the target grid cell: latitude is offset and
    longitude is scaled about the anchor by cos(anchor_lat)/cos(target_lat) so
    the copy keeps the source's true east-west ground width at its new latitude
    (see transform_all_coordinates).

    Returns (cloned, new_membership, airport_names, uuid_map) where cloned is a
    list of (type_name, element, new_uuid).
    """
    lat_offset = target_lat - anchor_lat
    cos_target = math.cos(math.radians(target_lat))
    lon_scale = (math.cos(math.radians(anchor_lat)) / cos_target
                 if abs(cos_target) > 1e-6 else 1.0)

    uuid_map = {old_uuid: generate_new_uuid() for old_uuid in collected_features}

    cloned = []
    for old_uuid, (feat_type, orig_elem) in collected_features.items():
        new_elem = copy.deepcopy(orig_elem)
        new_uuid = uuid_map[old_uuid]

        update_feature_ids(new_elem, new_uuid)
        update_xlink_refs(new_elem, uuid_map)
        transform_all_coordinates(
            new_elem, anchor_lon, target_lon, lat_offset, lon_scale)

        if begin_position is not None:
            update_valid_time(new_elem, begin_position)

        if feat_type == 'AirportHeliport':
            ts = None
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'AirportHeliportTimeSlice' in tag:
                    ts = child
                    break
            if ts is not None:
                n = ts.find('aixm:name', NSMAP)
                original_name = n.text if (n is not None and n.text) else None
                prefix = get_airport_designator_prefix(original_name)
                d = ts.find('aixm:designator', NSMAP)
                if d is not None and d.text and len(d.text) >= 2:
                    if prefix:
                        d.text = f"{prefix}{chr(ord('A') + index)}"
                    else:
                        d.text = f"{d.text[:-1]}{chr(ord('A') + index)}"
                    li = ts.find('aixm:locationIndicatorICAO', NSMAP)
                    if li is not None and li.text and li.text.strip():
                        li.text = d.text
                if n is not None and n.text:
                    n.text = n.text + f" {index + 1:02d}"
            xsi_nil = '{http://www.w3.org/2001/XMLSchema-instance}nil'
            alt_tag = '{http://www.aixm.aero/schema/5.1.1}altimeterSource'
            for asrc in new_elem.iter(alt_tag):
                if asrc.get(XLINK_HREF):
                    tail = asrc.tail
                    asrc.clear()
                    asrc.tail = tail
                    asrc.set(xsi_nil, 'true')
                    record_excluded_ref('AirportHeliport', 'altimeterSource')

        if feat_type in ('Navaid', *NAVAID_EQUIPMENT_TYPES):
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    break

        if feat_type == 'AeronauticalGroundLight':
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    break

        if feat_type == 'VerticalStructure':
            suffix = f"-{index + 1:02d}"
            for child in new_elem.iter():
                tag = child.tag
                if isinstance(tag, str) and 'TimeSlice' in tag and child is not new_elem:
                    n = child.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = n.text + suffix
                    for part_elem in child.iter(
                            '{http://www.aixm.aero/schema/5.1.1}VerticalStructurePart'):
                        pd = part_elem.find('aixm:designator', NSMAP)
                        if pd is not None and pd.text and pd.text.strip():
                            xsi_nil = pd.get('{http://www.w3.org/2001/XMLSchema-instance}nil')
                            if not xsi_nil:
                                parts = pd.text.split('-')
                                parts = [p.lstrip('0') or p for p in parts]
                                pd.text = '-'.join(parts) + suffix
                    for prop_name in VS_PROPERTIES_TO_REMOVE:
                        for prop_elem in list(child.findall(f'aixm:{prop_name}', NSMAP)):
                            child.remove(prop_elem)
                    break

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
                    di = child.find('aixm:designatorICAO', NSMAP)
                    if di is not None:
                        di.text = 'NO'
                        for attr in (
                            '{http://www.w3.org/2001/XMLSchema-instance}nil',
                            'nilReason',
                        ):
                            if attr in di.attrib:
                                del di.attrib[attr]
                    break

        if feat_type == 'ApronElement':
            xsi_nil = '{http://www.w3.org/2001/XMLSchema-instance}nil'
            supply_tag = '{http://www.aixm.aero/schema/5.1.1}supplyService'
            for ss in new_elem.iter(supply_tag):
                if ss.get(XLINK_HREF):
                    tail = ss.tail
                    ss.clear()
                    ss.tail = tail
                    ss.set(xsi_nil, 'true')
                    record_excluded_ref('ApronElement', 'supplyService')

        cloned.append((feat_type, new_elem, new_uuid))

    new_membership = {}
    airport_names = {}
    for old_uuid, old_airport_uuid in airport_membership.items():
        new_feat_uuid = uuid_map.get(old_uuid)
        new_ahp_uuid = uuid_map.get(old_airport_uuid)
        if new_feat_uuid and new_ahp_uuid:
            new_membership[new_feat_uuid] = new_ahp_uuid

    for feat_type, elem, new_uuid in cloned:
        if feat_type == 'AirportHeliport':
            name = get_airport_name(elem)
            if name:
                airport_names[new_uuid] = name

    return cloned, new_membership, airport_names, uuid_map


# ---------------------------------------------------------------------------
# Output document
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


def create_output_document(features, gml_id='Generated_Features', comment=None):
    root = etree.Element(
        '{http://www.aixm.aero/schema/5.1.1/message}AIXMBasicMessage',
        nsmap=OUTPUT_NSMAP,
    )
    root.set('{http://www.w3.org/2001/XMLSchema-instance}schemaLocation', SCHEMA_LOCATION)
    root.set(GML_ID, gml_id)

    for feat_tuple in features:
        elem = feat_tuple[1]
        member = etree.SubElement(
            root, '{http://www.aixm.aero/schema/5.1.1/message}hasMember')
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
    r"(<\?xml[^?]*\?>)\s*(<!--.*?-->)?\s*(<message:AIXMBasicMessage)([^>]*)>",
    re.DOTALL,
)
_ATTR_RE = re.compile(r'(\S+?="[^"]*")')


def _format_root_header(path):
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
    tree.write(path, encoding='UTF-8', xml_declaration=True, pretty_print=False)
    _format_root_header(path)


def write_organisation_authorities(root, out_dir, begin_position=None,
                                   exclude_uuids=None):
    """Write the OrganisationAuthority features from the baseline into a single
    Donlon_OrganisationAuthority.xml in out_dir.

    The features are copied verbatim and keep their original UUIDs, so the
    theOrganisationAuthority / specialDateAuthority references that the per-copy
    files leave pointing at the baseline resolve against this shared file.  When
    begin_position is given (the user's --effectiveDateStart) every
    validTime / featureLifetime beginPosition is set to it, matching the copies.

    Any OrganisationAuthority whose gml:identifier is in exclude_uuids is skipped
    (used to leave out the Donlon State and Donlon CAA authorities, which the user
    supplies themselves via --state-uuid / --caa-uuid).

    Returns the number of OrganisationAuthority features written.
    """
    exclude_uuids = exclude_uuids or set()
    feats = []
    for member in root.findall('message:hasMember', NSMAP):
        oa = member.find('aixm:OrganisationAuthority', NSMAP)
        if oa is None:
            continue
        oa_uuid = get_feature_uuid(oa)
        if oa_uuid in exclude_uuids:
            continue
        elem = copy.deepcopy(oa)
        if begin_position is not None:
            update_valid_time(elem, begin_position)
        feats.append(('OrganisationAuthority', elem, oa_uuid))
    if not feats:
        return 0
    path = os.path.join(out_dir, 'Donlon_OrganisationAuthority.xml')
    doc = create_output_document(
        feats, gml_id='Donlon_OrganisationAuthority',
        comment='Donlon OrganisationAuthority features (shared across all copies)')
    write_xml(doc, path)
    return len(feats)


# ---------------------------------------------------------------------------
# Temporality use-case replication
# ---------------------------------------------------------------------------


def _find_member_feature(member):
    """Return the single aixm:* feature element inside a message:hasMember."""
    for child in member:
        if isinstance(child.tag, str) and child.tag.startswith(AIXM_NS):
            return child
    return None


def _set_seq1_begin_positions(ts, vt_begin, fl_begin, date_map=None):
    """Set validTime/featureLifetime beginPosition on a TimeSlice if its
    sequenceNumber is 1.  None values are left untouched.  When date_map is
    given, record the replaced original date -> new date so the same change can
    be mirrored in the leading scenario comment."""
    seq = ts.find('aixm:sequenceNumber', NSMAP)
    if seq is None or not (seq.text and seq.text.strip() == '1'):
        return
    if vt_begin is not None:
        bp = ts.find('gml:validTime/gml:TimePeriod/gml:beginPosition', NSMAP)
        if bp is not None:
            if date_map is not None and bp.text and bp.text != vt_begin:
                date_map[bp.text] = vt_begin
            bp.text = vt_begin
    if fl_begin is not None:
        bp = ts.find('aixm:featureLifetime/gml:TimePeriod/gml:beginPosition', NSMAP)
        if bp is not None:
            if date_map is not None and bp.text and bp.text != fl_begin:
                date_map[bp.text] = fl_begin
            bp.text = fl_begin


# Opening tag of the AIXM message root, used to splice the original (verbatim)
# header onto the lxml-serialised body so the root attribute layout, leading
# comments and the blank line before the root are preserved exactly.
_TC_ROOT_RE = re.compile(r'<message:AIXMBasicMessage\b[^>]*>', re.DOTALL)

# Template files named "<base>_<N>-<descriptor>.xml" (multi-part scenarios) are
# shortened to "<base>_part-<N>.xml"; single-part files keep their base name.
_TC_PART_RE = re.compile(r'^(.*)_(\d+)-.+\.xml$')


def temporality_output_filename(template_basename):
    """Map a template file name to its shortened per-copy output name."""
    m = _TC_PART_RE.match(template_basename)
    if m:
        return f'{m.group(1)}_part-{m.group(2)}.xml'
    return template_basename


def write_temporality_cases(template_dir, copy_dir, copy_num, uuid_map,
                            orig_to_clone, anchor_lon, target_lon, lat_offset,
                            lon_scale, copy_begin=None, apply_adm_fix=False,
                            oa_uuid_map=None):
    """
    Replicate the temporality use-case templates into
    `copy_dir/Temporality_cases_NN/`, one file per template.  Multi-part template
    names `<base>_<N>-<descriptor>.xml` are shortened to `<base>_part-<N>.xml`;
    single-part names are kept as-is (see `temporality_output_filename`).

    Every feature is moved to this copy's position with the same latitude-offset
    + longitude-scale transform the per-copy clone received, so the temporality
    feature is co-located with the copy's clone.

    Normal files (feature exists in the baseline) are made consistent with the
    per-copy clone: remap the feature's own gml:id / gml:identifier to the clone
    UUID, remap every xlink:href urn:uuid: reference via uuid_map, set
    aixm:name / aixm:designator (in every TimeSlice) to the clone's, and sync the
    sequenceNumber=1 begin positions to the clone's.

    New-feature files (TEMPORALITY_NEW_FEATURE_FILES) hold a feature absent from
    the baseline: it gets a fresh random gml:id / gml:identifier, its xlink:href
    references are still remapped, and the seq=1 begin positions are set to the
    copy set's start time (copy_begin).  That fresh UUID is remembered for the
    copy, so a later normal file that updates the same brand-new feature (e.g. the
    Decommissioning-within-a-Committed-Baseline case updating the Commissioning
    case) reuses it and stays consistent instead of being reported as unmapped.

    When apply_adm_fix is True, the same limit (UNL/GND/FLOOR/CEILING +
    references) and Timesheet startDate/endDate corrections applied to the copied
    baseline are also applied to each template before remapping.

    The leading comment of each generated file is updated to match the copy: the
    baseline initial start date (TEMPORALITY_BASELINE_START) is find/replaced with
    the copy's start date, and every feature's original UUID is replaced with its
    per-copy UUID (e.g. the WorkArea UUID quoted in the work-area scenarios).

    Returns (files_written, warnings) where warnings is a list of
    (template_filename, original_uuid) for features that have no clone.
    """
    if not template_dir or not os.path.isdir(template_dir):
        return 0, []

    templates = sorted(f for f in os.listdir(template_dir)
                       if f.lower().endswith('.xml'))
    if not templates:
        return 0, []

    out_dir = os.path.join(copy_dir, f'{TEMPORALITY_OUTPUT_DIRNAME}_{copy_num:02d}')
    os.makedirs(out_dir, exist_ok=True)

    # UUID assigned to each newly-commissioned feature (template UUID -> per-copy
    # UUID), shared across the templates of this copy so that a later file
    # referring to the same brand-new feature reuses its UUID.  Templates are
    # processed in sorted order, so Commissioning_of_a_Feature.xml is handled
    # before the Decommissioning_..._Committed_Baseline.xml that updates it.
    shared_new_uuids = {}

    warnings = []
    written = 0
    for base in templates:
        is_new_feature = base in TEMPORALITY_NEW_FEATURE_FILES
        template_path = os.path.join(template_dir, base)
        with open(template_path, encoding='utf-8') as fh:
            orig_text = fh.read()
        tree = etree.parse(template_path)
        root = tree.getroot()

        # Same limit/timesheet corrections as the copied baseline features, so
        # the temporality use-case features stay consistent with their clones.
        if apply_adm_fix:
            run_adm_fixes(root)

        # Point the Donlon State / CAA OrganisationAuthority references at the
        # user-supplied UUIDs, matching the copied baseline.
        if oa_uuid_map:
            replace_uuid_everywhere(root, oa_uuid_map)

        date_map = {}  # original begin-position date -> new date (for the comment)
        comment_remap = {}  # original feature UUID -> per-copy UUID (for the comment)

        for member in root.findall('message:hasMember', NSMAP):
            feat = _find_member_feature(member)
            if feat is None:
                continue
            old_uuid = get_feature_uuid(feat)
            if not old_uuid:
                continue

            # Apply any source position override, then move the feature to this
            # copy's position with the same transform the clone received.
            if old_uuid in POSITION_OVERRIDES:
                lat, lon = POSITION_OVERRIDES[old_uuid]
                for pos in feat.iter(GML_POS):
                    pos.text = f"{lat} {lon}"
            transform_all_coordinates(feat, anchor_lon, target_lon, lat_offset, lon_scale)

            def _set_new_identity(new_uuid):
                """Assign a brand-new identity to feat, remap references and set the
                seq=1 begin positions to the copy set start time (copy_begin)."""
                feat.set(GML_ID, f'uuid.{new_uuid}')
                ident = feat.find('gml:identifier', NSMAP)
                if ident is not None:
                    ident.text = new_uuid
                update_xlink_refs(feat, uuid_map)
                for ts in feat.iter():
                    tag = ts.tag
                    if isinstance(tag, str) and 'TimeSlice' in tag and ts is not feat:
                        _set_seq1_begin_positions(ts, copy_begin, copy_begin, date_map)

            if is_new_feature:
                # Brand-new feature: fresh identity, recorded so a later file that
                # updates the same feature reuses this UUID.
                new_uuid = generate_new_uuid()
                shared_new_uuids[old_uuid] = new_uuid
                _set_new_identity(new_uuid)
                comment_remap[old_uuid] = new_uuid
                continue

            new_uuid = uuid_map.get(old_uuid)
            clone_info = orig_to_clone.get(old_uuid)
            if new_uuid is None or clone_info is None:
                # No baseline clone.  If this is the same brand-new feature created
                # by a new-feature file (e.g. the Commissioning case), reuse that
                # UUID so the two files stay consistent; otherwise it is genuinely
                # unmapped and left untouched.
                if old_uuid in shared_new_uuids:
                    reused = shared_new_uuids[old_uuid]
                    _set_new_identity(reused)
                    comment_remap[old_uuid] = reused
                else:
                    warnings.append((base, old_uuid))
                continue
            _clone_type, clone_elem = clone_info

            # 1. Remap the feature's own identity to the per-copy clone.
            feat.set(GML_ID, f'uuid.{new_uuid}')
            ident = feat.find('gml:identifier', NSMAP)
            if ident is not None:
                ident.text = new_uuid
            comment_remap[old_uuid] = new_uuid

            # 2. Remap every xlink:href urn:uuid: reference.
            update_xlink_refs(feat, uuid_map)

            # 3. Values to mirror from the clone.
            new_name = get_feature_name(clone_elem)
            new_desig = get_feature_designator(clone_elem)
            vt_begin, fl_begin = get_feature_begin_positions(clone_elem)

            # 4. Apply to each TimeSlice of the template feature.
            for ts in feat.iter():
                tag = ts.tag
                if not (isinstance(tag, str) and 'TimeSlice' in tag and ts is not feat):
                    continue
                if new_name is not None:
                    n = ts.find('aixm:name', NSMAP)
                    if n is not None and n.text:
                        n.text = new_name
                if new_desig is not None:
                    d = ts.find('aixm:designator', NSMAP)
                    if d is not None and d.text:
                        d.text = new_desig
                _set_seq1_begin_positions(ts, vt_begin, fl_begin, date_map)

        # Preserve the original header verbatim, mirror the begin-position changes
        # into the comment dates, and splice on the lxml-serialised body.
        m_orig = _TC_ROOT_RE.search(orig_text)
        body_text = etree.tostring(root, encoding='unicode')
        m_body = _TC_ROOT_RE.search(body_text)
        if m_orig and m_body:
            header = orig_text[:m_orig.end()]
            for old_date, new_date in date_map.items():
                if new_date and new_date != old_date:
                    header = header.replace(old_date, new_date)
            out_text = header + body_text[m_body.end():]
            if not out_text.endswith('\n'):
                out_text += '\n'
        else:
            out_text = body_text

        # Update the leading comment (and any remaining body occurrences) to match
        # this copy: shift the baseline initial start date to the copy's start
        # date, and reflect each feature's per-copy UUID (e.g. the WorkArea UUID in
        # the work-area scenarios).
        if copy_begin:
            out_text = out_text.replace(TEMPORALITY_BASELINE_START, copy_begin)
        for old_u, new_u in comment_remap.items():
            out_text = out_text.replace(old_u, new_u)
        if oa_uuid_map:
            for old_u, new_u in oa_uuid_map.items():
                out_text = out_text.replace(old_u, new_u)

        out_path = os.path.join(out_dir, temporality_output_filename(base))
        with open(out_path, 'w', encoding='utf-8', newline='\n') as fh:
            fh.write(out_text)
        written += 1

    return written, warnings


def _yesno(value):
    v = value.strip().lower()
    if v in ('yes', 'y', 'true', '1'):
        return True
    if v in ('no', 'n', 'false', '0'):
        return False
    raise argparse.ArgumentTypeError(f"expected yes/no, got '{value}'")


# ---------------------------------------------------------------------------
# Optional ADM fixes (self-contained; mirrors create_donlon_all_baseline_ADM_fix.py)
# ---------------------------------------------------------------------------
# Limit (UNL/GND/FLOOR/CEILING + upper/lowerLimitReference) and Timesheet
# startDate/endDate corrections, embedded here so this script runs standalone in
# a repository without depending on the ADM-fix tool.  The ADM-fix tool's feature
# removal is intentionally NOT included.

MSG_NS = '{http://www.aixm.aero/schema/5.1.1/message}'
XSI_NIL = '{http://www.w3.org/2001/XMLSchema-instance}nil'
ADM_UPPER = AIXM_NS + 'upperLimit'
ADM_LOWER = AIXM_NS + 'lowerLimit'
ADM_UPPER_REF = AIXM_NS + 'upperLimitReference'
ADM_LOWER_REF = AIXM_NS + 'lowerLimitReference'
ADM_TIMESHEET = AIXM_NS + 'Timesheet'
ADM_TIME_INTERVAL = AIXM_NS + 'timeInterval'
ADM_TIME_REFERENCE = AIXM_NS + 'timeReference'
ADM_START_DATE = AIXM_NS + 'startDate'
ADM_END_DATE = AIXM_NS + 'endDate'
FT_PER_M = 1.0 / 0.3048

# Parents that carry an upper/lowerLimit + reference pair handled by the rules.
_LIMIT_PARENTS = {
    'AirspaceLayer', 'AirspaceVolume', 'RouteSegmentTimeSlice',
    'HoldingPatternTimeSlice',
}


def _adm_is_nil(elem):
    return elem is not None and elem.get(XSI_NIL) == 'true'


def _adm_limit_to_feet(value_text, uom):
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


def _adm_set_limit(elem, value_text, uom):
    """Set a limit element's text/uom and clear any xsi:nil / nilReason."""
    elem.text = value_text
    if uom:
        elem.set('uom', uom)
    elif 'uom' in elem.attrib:
        del elem.attrib['uom']
    for attr in (XSI_NIL, 'nilReason'):
        if attr in elem.attrib:
            del elem.attrib[attr]


def _adm_reference_text(ref):
    """Textual value of an upper/lowerLimitReference, or None if absent, nil or
    empty."""
    if ref is None or ref.get(XSI_NIL) == 'true':
        return None
    return ref.text.strip() if (ref.text and ref.text.strip()) else None


def _adm_ref_missing(ref):
    return _adm_reference_text(ref) is None


def _adm_set_reference(parent, limit_elem, ref_tag, value):
    """Set the upper/lowerLimitReference (ref_tag) belonging to limit_elem to
    value, creating it immediately after limit_elem (keeping schema order) if it
    does not exist, and clearing any xsi:nil / nilReason."""
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


def _adm_make_aixm(local_name, text, tail):
    e = etree.Element(AIXM_NS + local_name)
    e.text = text
    e.tail = tail
    return e


def adm_translate_unl(root):
    """upperLimit UNL -> uom=FL 999 with upperLimitReference STD.  Done before GND
    so an UNL sibling counts as FL and makes a GND lowerLimit 0 FT MSL."""
    n = 0
    for up in root.iter(ADM_UPPER):
        if up.text and up.text.strip() == 'UNL':
            _adm_set_limit(up, '999', 'FL')
            parent = up.getparent()
            if parent is not None:
                _adm_set_reference(parent, up, ADM_UPPER_REF, 'STD')
            n += 1
    return n


def adm_translate_gnd(root):
    """lowerLimit GND -> 0 with its reference taken from the upper limit (UNL is
    already translated to FL by this point):
      - upper in FL  -> lowerLimit 0 FT, lowerLimitReference MSL;
      - upper in FT/M carrying a reference -> lowerLimit 0 <upper uom>,
        lowerLimitReference identical to the upper limit's reference;
      - otherwise (no usable upper) -> 0 (FT if the upper is FT/FL else M)."""
    n = 0
    for low in root.iter(ADM_LOWER):
        if not (low.text and low.text.strip() == 'GND'):
            continue
        parent = low.getparent()
        if parent is None:
            continue
        up = parent.find(ADM_UPPER)
        up_uom = up.get('uom') if up is not None else None
        up_ref = _adm_reference_text(parent.find(ADM_UPPER_REF))
        if up_uom == 'FL':
            _adm_set_limit(low, '0', 'FT')
            _adm_set_reference(parent, low, ADM_LOWER_REF, 'MSL')
        elif up_uom in ('FT', 'M') and up_ref is not None:
            _adm_set_limit(low, '0', up_uom)
            _adm_set_reference(parent, low, ADM_LOWER_REF, up_ref)
        else:
            _adm_set_limit(low, '0', 'FT' if up_uom in ('FT', 'FL') else 'M')
        n += 1
    return n


def _adm_gather_volume_extremes(airspace, uuid_map, seen, lowers, uppers):
    """Collect numeric AirspaceVolume upper/lower limits (with their references)
    from an airspace, recursing into referenced airspaces (the multi-part case)."""
    if id(airspace) in seen:
        return
    seen.add(id(airspace))
    for vol in airspace.iter(AIXM_NS + 'AirspaceVolume'):
        ul = vol.find(ADM_UPPER)
        ll = vol.find(ADM_LOWER)
        if ul is not None and not _adm_is_nil(ul):
            f = _adm_limit_to_feet(ul.text, ul.get('uom'))
            if f is not None:
                uppers.append((f, ul.text, ul.get('uom'),
                               _adm_reference_text(vol.find(ADM_UPPER_REF))))
        if ll is not None and not _adm_is_nil(ll):
            f = _adm_limit_to_feet(ll.text, ll.get('uom'))
            if f is not None:
                lowers.append((f, ll.text, ll.get('uom'),
                               _adm_reference_text(vol.find(ADM_LOWER_REF))))
    for dep in airspace.iter(AIXM_NS + 'theAirspace'):
        href = dep.get(XLINK_HREF)
        if href and href.startswith('urn:uuid:'):
            ref = uuid_map.get(href[len('urn:uuid:'):])
            if ref is not None:
                _adm_gather_volume_extremes(ref, uuid_map, seen, lowers, uppers)


def _adm_airspace_volume_extremes(airspace, uuid_map):
    """(lowest_lower, highest_upper) as (value_text, uom, reference); None when
    not resolvable."""
    lowers, uppers = [], []
    _adm_gather_volume_extremes(airspace, uuid_map, set(), lowers, uppers)
    lowest = min(lowers, key=lambda t: t[0])[1:] if lowers else None
    highest = max(uppers, key=lambda t: t[0])[1:] if uppers else None
    return lowest, highest


def _adm_build_airspace_uuid_map(root):
    uuid_map = {}
    for member in root.findall(MSG_NS + 'hasMember'):
        airspace = member.find(AIXM_NS + 'Airspace')
        if airspace is None:
            continue
        ident = airspace.find(GML_IDENTIFIER)
        if ident is not None and ident.text:
            uuid_map[ident.text.strip()] = airspace
    return uuid_map


def adm_substitute_airspace_floor_ceiling(root):
    """Replace FLOOR / CEILING tokens in each Airspace's AirspaceLayers with the
    airspace's lowest / highest volume limits, copying that volume limit's
    reference onto the layer too."""
    uuid_map = _adm_build_airspace_uuid_map(root)
    replaced = 0
    warnings = []
    for member in root.findall(MSG_NS + 'hasMember'):
        airspace = member.find(AIXM_NS + 'Airspace')
        if airspace is None:
            continue
        lowest, highest = _adm_airspace_volume_extremes(airspace, uuid_map)
        for low in airspace.iter(ADM_LOWER):
            if low.text and low.text.strip() == 'FLOOR':
                if lowest is None:
                    warnings.append((airspace, 'FLOOR'))
                    continue
                _adm_set_limit(low, lowest[0], lowest[1])
                if lowest[2]:
                    _adm_set_reference(low.getparent(), low, ADM_LOWER_REF, lowest[2])
                replaced += 1
        for up in airspace.iter(ADM_UPPER):
            if up.text and up.text.strip() == 'CEILING':
                if highest is None:
                    warnings.append((airspace, 'CEILING'))
                    continue
                _adm_set_limit(up, highest[0], highest[1])
                if highest[2]:
                    _adm_set_reference(up.getparent(), up, ADM_UPPER_REF, highest[2])
                replaced += 1
    return replaced, warnings


def adm_substitute_routesegment_floor_ceiling(root):
    """Replace FLOOR / CEILING tokens in each RouteSegment's AirspaceLayers with
    the limits (value+uom+reference) found directly under the RouteSegmentTimeSlice."""
    replaced = 0
    warnings = []
    for member in root.findall(MSG_NS + 'hasMember'):
        rsg = member.find(AIXM_NS + 'RouteSegment')
        if rsg is None:
            continue
        ts = None
        for child in rsg.iter():
            if isinstance(child.tag, str) and 'RouteSegmentTimeSlice' in child.tag:
                ts = child
                break
        if ts is None:
            continue
        direct_up = ts.find(ADM_UPPER)
        direct_low = ts.find(ADM_LOWER)
        direct_up_ref = _adm_reference_text(ts.find(ADM_UPPER_REF))
        direct_low_ref = _adm_reference_text(ts.find(ADM_LOWER_REF))
        for low in rsg.iter(ADM_LOWER):
            if low is direct_low:
                continue
            if low.text and low.text.strip() == 'FLOOR':
                if direct_low is None or _adm_is_nil(direct_low) or not direct_low.text:
                    warnings.append((rsg, 'FLOOR'))
                    continue
                _adm_set_limit(low, direct_low.text, direct_low.get('uom'))
                if direct_low_ref:
                    _adm_set_reference(low.getparent(), low, ADM_LOWER_REF, direct_low_ref)
                replaced += 1
        for up in rsg.iter(ADM_UPPER):
            if up is direct_up:
                continue
            if up.text and up.text.strip() == 'CEILING':
                if direct_up is None or _adm_is_nil(direct_up) or not direct_up.text:
                    warnings.append((rsg, 'CEILING'))
                    continue
                _adm_set_limit(up, direct_up.text, direct_up.get('uom'))
                if direct_up_ref:
                    _adm_set_reference(up.getparent(), up, ADM_UPPER_REF, direct_up_ref)
                replaced += 1
    return replaced, warnings


def adm_finalize_limit_references(root):
    """Fill any still-missing upper/lowerLimit reference: a limit in FL gets STD;
    an upper in FT/M carrying a reference is propagated to a lower limit still
    missing one.  Existing (non-nil) references are never overwritten.  Returns
    (fl_to_std_count, inherited_count)."""
    fl_std = 0
    inherited = 0
    for parent in root.iter():
        if not isinstance(parent.tag, str):
            continue
        if etree.QName(parent).localname not in _LIMIT_PARENTS:
            continue
        ul = parent.find(ADM_UPPER)
        ll = parent.find(ADM_LOWER)
        for lim, ref_tag in ((ul, ADM_UPPER_REF), (ll, ADM_LOWER_REF)):
            if lim is None or _adm_is_nil(lim):
                continue
            if lim.get('uom') == 'FL' and _adm_ref_missing(parent.find(ref_tag)):
                _adm_set_reference(parent, lim, ref_tag, 'STD')
                fl_std += 1
        if (ul is not None and not _adm_is_nil(ul) and ul.get('uom') in ('FT', 'M')
                and ll is not None and not _adm_is_nil(ll)):
            up_ref = _adm_reference_text(parent.find(ADM_UPPER_REF))
            if up_ref and _adm_ref_missing(parent.find(ADM_LOWER_REF)):
                _adm_set_reference(parent, ll, ADM_LOWER_REF, up_ref)
                inherited += 1
    return fl_std, inherited


def adm_fix_timesheets(root):
    """Add startDate 01-01 / endDate 31-12 (after timeReference) to every non-nil
    Timesheet that lacks them."""
    n = 0
    for ti in root.iter(ADM_TIME_INTERVAL):
        ts = ti.find(ADM_TIMESHEET)
        if ts is None:
            continue
        has_sd = ts.find(ADM_START_DATE) is not None
        has_ed = ts.find(ADM_END_DATE) is not None
        if has_sd and has_ed:
            continue
        tref = ts.find(ADM_TIME_REFERENCE)
        if tref is None:
            continue
        tail = tref.tail
        anchor = tref
        if not has_sd:
            sd = _adm_make_aixm('startDate', '01-01', tail)
            ts.insert(list(ts).index(anchor) + 1, sd)
            anchor = sd
        if not has_ed:
            ed = _adm_make_aixm('endDate', '31-12', tail)
            ts.insert(list(ts).index(anchor) + 1, ed)
        n += 1
    return n


def run_adm_fixes(root):
    """Apply every ADM limit + timesheet correction to root.  Returns
    (counts_dict, floor_ceiling_warnings)."""
    n_unl = adm_translate_unl(root)
    n_gnd = adm_translate_gnd(root)
    n_ase, w_ase = adm_substitute_airspace_floor_ceiling(root)
    n_rsg, w_rsg = adm_substitute_routesegment_floor_ceiling(root)
    n_fl, n_inh = adm_finalize_limit_references(root)
    n_ts = adm_fix_timesheets(root)
    counts = {'unl': n_unl, 'gnd': n_gnd, 'ase': n_ase, 'rsg': n_rsg,
              'fl': n_fl, 'inh': n_inh, 'ts': n_ts}
    return counts, (w_ase + w_rsg)


def apply_adm_fixes(root):
    """Apply the ADM limit/timesheet corrections to the source tree before
    features are extracted and cloned, so every copy inherits them, and print a
    summary."""
    print("Applying ADM fixes (limits + timesheets) to the source ...")
    counts, warnings = run_adm_fixes(root)
    print(f"  UNL upperLimit -> FL 999 STD:        {counts['unl']}")
    print(f"  GND lowerLimit -> 0 + reference:     {counts['gnd']}")
    print(f"  Airspace FLOOR/CEILING replaced:     {counts['ase']}")
    print(f"  RouteSegment FLOOR/CEILING replaced: {counts['rsg']}")
    print(f"  FL limits given reference STD:       {counts['fl']}")
    print(f"  Lower refs inherited from upper:     {counts['inh']}")
    print(f"  Timesheets startDate/endDate added:  {counts['ts']}")
    for elem, token in warnings:
        ident = elem.find(GML_IDENTIFIER)
        uid = ident.text if ident is not None else '?'
        print(f"  WARNING: could not resolve {token} for {uid}")
    print()


# ---------------------------------------------------------------------------
# Interactive prompting (used when the script is run with no CLI arguments)
# ---------------------------------------------------------------------------


def prompt_for_args():
    """Collect the run parameters interactively, one per line, when the script is
    started with no command-line arguments.  An empty answer or a single hyphen
    '-' leaves an optional field unset (default / None).  Returns a namespace with
    the same attributes argparse would produce."""
    max_copies = min(GRID_ROWS * GRID_COLS, MAX_AIRPORT_COPIES)

    def _opt(raw):
        return None if raw in ('', '-') else raw

    print("Use hyphen '-' to leave an optional input empty.")

    # input file location (required)
    while True:
        inp = input("input file location: ").strip().strip('"')
        if not inp or inp == '-':
            print("  An input file is required.")
            continue
        if not os.path.isfile(inp):
            print(f"  File not found: {inp}")
            continue
        break

    output = _opt(input("output directory location (optional): ").strip().strip('"'))

    while True:
        raw = input(f"number of copies (max {max_copies}): ").strip()
        if raw in ('', '-'):
            num_copies = 20
            break
        try:
            num_copies = int(raw)
        except ValueError:
            print("  Enter a whole number.")
            continue
        if 1 <= num_copies <= max_copies:
            break
        print(f"  Enter a number between 1 and {max_copies}.")

    while True:
        raw = input("inclusion radius around Donlon Intl. (default 40NM): ").strip()
        if raw in ('', '-'):
            radius_nm = 40.0
            break
        try:
            radius_nm = float(raw)
            break
        except ValueError:
            print("  Enter a radius in NM (number).")

    effective_date = _opt(input("effective date start: ").strip())
    temporality = _opt(input("temporality cases directory (optional): ").strip().strip('"'))

    while True:
        raw = input("apply ADM fix (yes/no): ").strip()
        if raw in ('', '-'):
            apply_adm = False
            break
        try:
            apply_adm = _yesno(raw)
            break
        except argparse.ArgumentTypeError:
            print("  Enter yes or no.")

    state_uuid = _opt(input("new state uuid (optional): ").strip())
    caa_uuid = _opt(input("new caa uuid (optional): ").strip())

    return argparse.Namespace(
        input=inp, output=output, num_copies=num_copies, radius_nm=radius_nm,
        exc_airspace_types=[], exc_features=[],
        effectiveDateStart=effective_date,
        temporality_cases_dir=temporality, apply_adm_fix=apply_adm,
        state_uuid=state_uuid, caa_uuid=caa_uuid)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description='Multiply the Donlon features in/near the Donlon TMA onto an '
                    'evenly-spaced grid that fits inside the EAAD FIR.')
    parser.add_argument('--input', '-i', required=True,
                        help='Path to the input AIXM XML file')
    parser.add_argument('--output', '-o', default=None,
                        help='Output folder (default: Donlon_Dataset_Copies next '
                             'to the script)')
    parser.add_argument('--num-copies', '-n', type=int, default=20,
                        help=f'Number of copies to make (default 20). They fill a '
                             f'{GRID_ROWS}x{GRID_COLS} grid from the top-left '
                             f'(north-west) towards the right and down. Must be '
                             f'between 1 and {min(GRID_ROWS * GRID_COLS, MAX_AIRPORT_COPIES)}.')
    parser.add_argument('--radius-nm', type=float, default=80.0,
                        help='Selection radius in NM around the TMA polygon edge '
                             '(default 80).')
    parser.add_argument('--exc-airspace-types', nargs='*', default=[], metavar='TYPE',
                        help='Extra Airspace types to exclude (FIR/FIR_P always '
                             'excluded).')
    parser.add_argument('--exc-features', nargs='*', default=[], metavar='DESIGNATOR',
                        help='Exclude features whose aixm:designator matches any '
                             'of the given values.')
    parser.add_argument('--effectiveDateStart', default=None,
                        help='validTime beginPosition for all copies '
                             '(e.g. 2026-06-02T00:00:00Z).')
    parser.add_argument('--temporality-cases-dir', default=None,
                        help='Folder of temporality use-case templates to '
                             f'replicate into every Donlon_Copy_NN as '
                             f'{TEMPORALITY_OUTPUT_DIRNAME}_NN. If not given, no '
                             'temporality cases are replicated.')
    parser.add_argument('--apply-ADM-fix', dest='apply_adm_fix', type=_yesno,
                        default=False, metavar='yes/no',
                        help='Apply the same limit (UNL/GND/FLOOR/CEILING + '
                             'references) and Timesheet startDate/endDate '
                             'corrections as create_donlon_all_baseline_ADM_fix.py '
                             'to the source before copying (default no).')
    parser.add_argument('--state-uuid', dest='state_uuid', default=None, metavar='UUID',
                        help='Replace every reference to the Donlon State '
                             f'OrganisationAuthority ({DONLON_STATE_OA_UUID}, '
                             '"REPUBLIC OF DONLON EA STATE") with this UUID in all '
                             'copies and their temporality cases.')
    parser.add_argument('--caa-uuid', dest='caa_uuid', default=None, metavar='UUID',
                        help='Replace every reference to the Donlon CAA '
                             f'OrganisationAuthority ({DONLON_CAA_OA_UUID}, '
                             '"DONLON CIVIL AVIATION ADMINISTRATION EA-CAA") with '
                             'this UUID in all copies and their temporality cases.')
    # Run interactively (prompt for each input on its own line) when started with
    # no command-line arguments; otherwise parse the CLI as usual.
    if len(sys.argv) == 1:
        args = prompt_for_args()
    else:
        args = parser.parse_args()

    # Build the OrganisationAuthority UUID substitution map from the optional
    # --state-uuid / --caa-uuid options (a leading urn:uuid: / uuid. prefix is
    # stripped).  Applied to the source tree before cloning so every clone, the
    # shared Donlon_OrganisationAuthority.xml and the temporality cases inherit it.
    def _norm_uuid(value):
        v = value.strip()
        for prefix in ('urn:uuid:', 'uuid.'):
            if v.lower().startswith(prefix):
                v = v[len(prefix):]
        return v

    oa_uuid_map = {}
    if args.state_uuid:
        oa_uuid_map[DONLON_STATE_OA_UUID] = _norm_uuid(args.state_uuid)
    if args.caa_uuid:
        oa_uuid_map[DONLON_CAA_OA_UUID] = _norm_uuid(args.caa_uuid)

    # Default output folder: Donlon_Dataset_Copies next to this script (version_2),
    # so copies don't land in the version_1 source folder.
    script_dir = os.path.dirname(os.path.abspath(__file__))
    if args.output is None:
        args.output = os.path.join(script_dir, 'Donlon_Dataset_Copies')

    # Resolve the temporality-cases template folder.  If none is specified, no
    # temporality cases are replicated.
    if args.temporality_cases_dir:
        temporality_dir = os.path.abspath(args.temporality_cases_dir)
    else:
        temporality_dir = None

    rows, cols = GRID_ROWS, GRID_COLS
    count = args.num_copies
    max_copies = min(rows * cols, MAX_AIRPORT_COPIES)
    if count < 1:
        parser.error('--num-copies must be >= 1')
    if count > max_copies:
        print(f"ERROR: --num-copies {count} exceeds the maximum of {max_copies} "
              f"(a {rows}x{cols} grid holds {rows * cols} cells and there is one "
              f"airport designator letter per copy, max {MAX_AIRPORT_COPIES}).")
        sys.exit(1)

    ase_types_exclude = AIRSPACE_TYPES_EXCLUDE_DEFAULT | set(args.exc_airspace_types)

    effective_start = None
    if args.effectiveDateStart:
        effective_start = datetime.fromisoformat(args.effectiveDateStart.replace('Z', '+00:00'))

    print("Configuration:")
    print(f"  Input:    {args.input}")
    print(f"  Output:   {args.output}")
    print(f"  Copies:   {count} (filling a {rows}x{cols} grid from the top-left)")
    print(f"  Radius:   {args.radius_nm} NM around the TMA edge")
    print(f"  Excluded airspace types: {', '.join(sorted(ase_types_exclude))}")
    if not temporality_dir:
        print("  Temporality cases: (none specified; skipped)")
    elif os.path.isdir(temporality_dir):
        print(f"  Temporality cases: {temporality_dir}")
    else:
        print(f"  Temporality cases: {temporality_dir}  (not found; skipped)")
    print(f"  Apply ADM fix: {'yes' if args.apply_adm_fix else 'no'}")
    if oa_uuid_map.get(DONLON_STATE_OA_UUID):
        print(f"  Donlon State OrganisationAuthority UUID -> {oa_uuid_map[DONLON_STATE_OA_UUID]}")
    if oa_uuid_map.get(DONLON_CAA_OA_UUID):
        print(f"  Donlon CAA OrganisationAuthority UUID   -> {oa_uuid_map[DONLON_CAA_OA_UUID]}")
    if args.exc_features:
        print(f"  Excluded feature designators: {', '.join(sorted(args.exc_features))}")
    if effective_start:
        print(f"  Effective date start: {args.effectiveDateStart}")
    print()

    print(f"Parsing {args.input} ...")
    tree = etree.parse(args.input)
    root = tree.getroot()

    # Optionally apply the ADM limit/timesheet corrections to the whole source
    # tree first, so every cloned copy inherits them.  Done before extraction so
    # FLOOR/CEILING can resolve against all airspace volumes in the input.
    if args.apply_adm_fix:
        apply_adm_fixes(root)

    # Replace the Donlon State / CAA OrganisationAuthority references with the
    # user-supplied UUIDs on the whole source tree, before extraction/cloning, so
    # every clone and the shared Donlon_OrganisationAuthority.xml inherit them.
    if oa_uuid_map:
        n_oa = replace_uuid_everywhere(root, oa_uuid_map)
        print(f"Replacing OrganisationAuthority references ... "
              f"{n_oa} occurrence(s) in the source.\n")

    # Override the location of selected features so they fall inside the TMA
    # selection and get cloned with the rest of the scene.
    if POSITION_OVERRIDES:
        print("Applying position overrides ...")
        for fuuid, name, old_pos, new_pos in apply_position_overrides(root):
            print(f"  {name or fuuid}: {old_pos} -> {new_pos}")
        print()

    # Locate the Donlon TMA polygon and the EAAD FIR polygon (fixed UUIDs).
    tma_polygon = find_airspace_polygon_by_uuid(root, DONLON_TMA_UUID)
    if not tma_polygon:
        parser.error(f"Donlon TMA airspace (uuid {DONLON_TMA_UUID}) not found in the input.")
    tma_lat, tma_lon = polygon_centroid(tma_polygon)
    tbb = polygon_bbox(tma_polygon)
    print(f"  TMA (uuid {DONLON_TMA_UUID}): {len(tma_polygon)} vertices, "
          f"centroid lat {tma_lat:.4f}, lon {tma_lon:.4f}")
    print(f"  TMA bbox: lat [{tbb[0]:.4f}, {tbb[1]:.4f}], lon [{tbb[2]:.4f}, {tbb[3]:.4f}]")

    fir_polygon = find_airspace_polygon_by_uuid(root, DONLON_FIR_UUID)
    if not fir_polygon:
        parser.error(f"EAAD FIR airspace (uuid {DONLON_FIR_UUID}) not found in the input.")
    fbb = polygon_bbox(fir_polygon)
    print(f"  EAAD FIR (uuid {DONLON_FIR_UUID}): {len(fir_polygon)} vertices, "
          f"bbox lat [{fbb[0]:.4f}, {fbb[1]:.4f}], lon [{fbb[2]:.4f}, {fbb[3]:.4f}]")
    print()

    # Extract and collect candidate features.
    print("Extracting features by type ...")
    features_by_type = extract_features_by_type(root)
    for ft in FEATURE_TYPES:
        print(f"  {ft}: {len(features_by_type[ft])} total in file")

    collected, airport_membership, navaid_equipment = collect_features(
        features_by_type, ase_types_exclude)

    # Spatial filter: keep only features in/near the TMA.
    kept, dropped_no_geom = spatial_filter(
        collected, airport_membership, navaid_equipment, tma_polygon, args.radius_nm)

    # Optional --exc-features filter.
    exc_designators = set(args.exc_features)
    if exc_designators:
        excluded_feats = []
        for fuuid in list(kept):
            ftype, felem = kept[fuuid]
            desig = get_feature_designator(felem)
            if desig and desig in exc_designators:
                excluded_feats.append((ftype, desig))
                del kept[fuuid]
                airport_membership.pop(fuuid, None)
        if excluded_feats:
            print("\n  Excluded by --exc-features:")
            for ftype, desig in excluded_feats:
                print(f"    {ftype} designator={desig}")

    # Restrict membership to kept features.
    airport_membership = {u: a for u, a in airport_membership.items()
                          if u in kept and a in kept}

    print(f"\n  Selected (in TMA or within {args.radius_nm:.0f} NM): "
          f"{len(kept)} feature(s)")
    sel_by_type = defaultdict(int)
    for ftype, _ in kept.values():
        sel_by_type[ftype] += 1
    for ft in FEATURE_TYPES:
        if sel_by_type.get(ft):
            print(f"    {ft}: {sel_by_type[ft]}")
    kept_airports = [get_airport_name(e) or get_feature_designator(e)
                     for t, e in kept.values() if t == 'AirportHeliport']
    print(f"    Airports kept: {', '.join(sorted(a for a in kept_airports if a))}")
    if dropped_no_geom:
        print(f"  Skipped (no own geometry to locate): "
              f"{', '.join(d or '?' for _, d in dropped_no_geom)}")

    # Place `count` copy cells on the fixed rows x cols frame with equal ground
    # spacing both ways, centred in the EAAD FIR bbox and filled from the
    # top-left; a partial last row is centred horizontally.
    grid = build_fir_grid(fir_polygon, rows, cols, count, MARGIN_FRAC)
    pulled = sum(1 for c in grid if c['pulled'])
    print(f"\n  Grid: {count} copy cell(s) filling a {rows}x{cols} frame from the "
          f"top-left with equal horizontal/vertical spacing, last row centred "
          f"({pulled} cell(s) pulled inward to stay inside the FIR)")

    # Generate the copies: latitude offset + longitude scaled about the anchor
    # so each copy keeps the source's true ground shape at its new latitude.
    print(f"\nGenerating {count} copies ({count * len(kept)} features total) ...")
    all_cloned = []
    per_copy_data = []
    for cell in grid:
        i = cell['index']
        copy_num = i + 1
        lat_offset = cell['lat'] - tma_lat
        cos_target = math.cos(math.radians(cell['lat']))
        lon_scale = (math.cos(math.radians(tma_lat)) / cos_target
                     if abs(cos_target) > 1e-6 else 1.0)

        copy_begin = None
        if effective_start is not None:
            copy_begin = effective_start.strftime('%Y-%m-%dT%H:%M:%SZ')

        time_info = f"  validTime.beginPosition={copy_begin}" if copy_begin else ""
        print(f"  Copy {copy_num:02d}: grid (row {cell['row']}, col {cell['col']}) "
              f"-> lat {cell['lat']:.4f}, lon {cell['lon']:.4f}  "
              f"(lat offset {lat_offset:+.4f}, lon scale {lon_scale:.4f}){time_info}")

        cloned, new_membership, airport_names, uuid_map = clone_feature_set(
            kept, airport_membership, i, tma_lat, tma_lon, cell['lat'], cell['lon'],
            begin_position=copy_begin)

        # old_uuid -> (type, clone_elem), for syncing the temporality cases.
        new_to_old = {new: old for old, new in uuid_map.items()}
        orig_to_clone = {new_to_old[nu]: (ft, el)
                         for ft, el, nu in cloned if nu in new_to_old}
        transform_params = (tma_lon, cell['lon'], lat_offset, lon_scale)

        per_copy_data.append((cloned, new_membership, airport_names, uuid_map,
                              orig_to_clone, transform_params, copy_begin))
        all_cloned.extend(cloned)

    print_excluded_refs_summary()

    # --- Write outputs ---
    out_dir = os.path.abspath(args.output)
    os.makedirs(out_dir, exist_ok=True)

    all_file = os.path.join(out_dir, 'Donlon_Dataset_Copies_ALL.xml')
    print(f"\nBuilding {all_file} ...")
    all_tree = create_output_document(
        all_cloned, gml_id='Donlon_Dataset_Copies_ALL',
        comment='Generated Donlon TMA-area dataset copies')
    write_xml(all_tree, all_file)
    print(f"  {len(all_cloned)} features written.")

    # Shared OrganisationAuthority features: the per-copy files reference these
    # (theOrganisationAuthority / specialDateAuthority) but don't contain them,
    # so emit them once, verbatim (original UUIDs), at the effective start date.
    org_begin = effective_start.strftime('%Y-%m-%dT%H:%M:%SZ') if effective_start else None
    # Exclude the Donlon State and CAA authorities from the shared file (the user
    # supplies their own).  Cover both the original baseline UUIDs and any
    # user-supplied replacements, since references in root were already rewritten.
    org_exclude = {DONLON_STATE_OA_UUID, DONLON_CAA_OA_UUID} | set(oa_uuid_map.values())
    n_org = write_organisation_authorities(
        root, out_dir, begin_position=org_begin, exclude_uuids=org_exclude)
    org_date_info = f" (beginPosition={org_begin})" if org_begin else ""
    print(f"  Donlon_OrganisationAuthority.xml: {n_org} OrganisationAuthority "
          f"feature(s) written{org_date_info}.")

    COMMON_ONLY_TYPES = {
        'VerticalStructure', 'Airspace', 'DesignatedPoint', 'AeronauticalGroundLight',
        'Navaid', 'VOR', 'DME', 'NDB', 'TACAN', 'Localizer', 'Glidepath', 'MarkerBeacon',
    }
    AIRPORT_OR_COMMON_TYPES = {
        'AirportHeliport', 'Runway', 'RunwayDirection', 'RunwayElement',
        'RunwayCentrelinePoint', 'TouchDownLiftOff', 'Taxiway', 'TaxiwayElement',
        'Apron', 'ApronElement', 'AircraftStand', 'WorkArea',
    }

    temporality_total = 0
    temporality_warnings = []

    print("\nWriting per-copy folders ...")
    for i, (copy_features, new_membership, airport_names, uuid_map, orig_to_clone,
            transform_params, copy_begin) in enumerate(per_copy_data):
        copy_num = i + 1
        copy_dir = os.path.join(out_dir, f'Donlon_Copy_{copy_num:02d}')
        os.makedirs(copy_dir, exist_ok=True)

        common_features = []
        airport_features = {}
        for feat_type, elem, new_uuid in copy_features:
            if feat_type in COMMON_ONLY_TYPES:
                common_features.append((feat_type, elem, new_uuid))
            elif feat_type in AIRPORT_OR_COMMON_TYPES:
                ahp_uuid = new_membership.get(new_uuid)
                if ahp_uuid:
                    airport_features.setdefault(ahp_uuid, []).append(
                        (feat_type, elem, new_uuid))
                else:
                    common_features.append((feat_type, elem, new_uuid))

        common_dir = os.path.join(copy_dir, f'Common_{copy_num:02d}')
        os.makedirs(common_dir, exist_ok=True)
        common_by_type = {}
        for feat_type, elem, new_uuid in common_features:
            common_by_type.setdefault(feat_type, []).append((feat_type, elem, new_uuid))
        for feat_type, feat_list in common_by_type.items():
            fpath = os.path.join(common_dir, f'{feat_type}_{copy_num:02d}.xml')
            doc = create_output_document(
                feat_list, gml_id=f'{feat_type}_Copy_{copy_num:02d}',
                comment=f'{feat_type} features - Copy {copy_num:02d}')
            write_xml(doc, fpath)

        ahp_parent_dir = os.path.join(
            copy_dir, f'AirportHeliport_related_features_{copy_num:02d}')
        os.makedirs(ahp_parent_dir, exist_ok=True)
        for ahp_uuid, ahp_features in airport_features.items():
            ahp_name = airport_names.get(ahp_uuid, ahp_uuid)
            folder_name = re.sub(r'[/\\. ]+', '_', ahp_name).strip('_')
            ahp_dir = os.path.join(ahp_parent_dir, folder_name)
            os.makedirs(ahp_dir, exist_ok=True)
            ahp_by_type = {}
            for feat_type, elem, new_uuid in ahp_features:
                ahp_by_type.setdefault(feat_type, []).append((feat_type, elem, new_uuid))
            for feat_type, feat_list in ahp_by_type.items():
                fpath = os.path.join(ahp_dir, f'{feat_type}_{copy_num:02d}.xml')
                doc = create_output_document(
                    feat_list, gml_id=f'{feat_type}_Copy_{copy_num:02d}',
                    comment=f'{feat_type} features - Copy {copy_num:02d}')
                write_xml(doc, fpath)

        ordered_features = []
        for ft in ALL_FEATURES_ORDER:
            for feat_type, elem, new_uuid in copy_features:
                if feat_type == ft:
                    ordered_features.append((feat_type, elem, new_uuid))
        all_feat_path = os.path.join(copy_dir, f'Donlon_ALL_Baseline_{copy_num:02d}.xml')
        all_feat_doc = create_output_document(
            ordered_features, gml_id=f'All_features_Copy_{copy_num:02d}',
            comment=f'All features - Copy {copy_num:02d}')
        write_xml(all_feat_doc, all_feat_path)

        # Temporality use-cases for this copy: same scene transform as the clone.
        anchor_lon, target_lon, lat_offset, lon_scale = transform_params
        tc_written, tc_warnings = write_temporality_cases(
            temporality_dir, copy_dir, copy_num, uuid_map, orig_to_clone,
            anchor_lon, target_lon, lat_offset, lon_scale, copy_begin=copy_begin,
            apply_adm_fix=args.apply_adm_fix, oa_uuid_map=oa_uuid_map)
        temporality_total += tc_written
        temporality_warnings.extend(tc_warnings)
        tc_info = (f" + {TEMPORALITY_OUTPUT_DIRNAME}_{copy_num:02d}/ ({tc_written} file(s))"
                   if tc_written else "")

        print(f"  Donlon_Copy_{copy_num:02d}/: Common/ + "
              f"{len(airport_features)} airport folder(s) + "
              f"Donlon_ALL_Baseline_{copy_num:02d}.xml{tc_info}, "
              f"{len(copy_features)} features")

    if temporality_dir and os.path.isdir(temporality_dir):
        print(f"\nTemporality cases: {temporality_total} file(s) written across "
              f"{count} copy set(s) from {temporality_dir}")
        if temporality_warnings:
            unmapped = sorted({(b, u) for b, u in temporality_warnings})
            print(f"  WARNING: {len(unmapped)} feature(s) had no clone (left "
                  f"untouched); e.g.:")
            for b, u in unmapped[:5]:
                print(f"    {b}: {u}")
    elif temporality_dir:
        print(f"\nTemporality cases: template folder not found at "
              f"{temporality_dir}; skipped.")

    print(f"\nDone!  {len(all_cloned)} features total in {out_dir}")
    return 0


if __name__ == '__main__':
    exit(main())
