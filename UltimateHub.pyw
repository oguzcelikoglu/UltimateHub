#!/usr/bin/env python3
"""
UltimateHub - everything in ONE file.

  * Hub        : Windows-7 "Aero" styled launcher (this file, no extra modules)
  * OpenImage  : image metadata cleaner / converter, with optional
                 "Write random EXIF" (replaces the metadata with realistic
                 data of a random phone from a built-in list of 30 models)
  * NuMouse    : numpad mouse controller. It runs as a background helper:
                 the Hub starts a second copy of this very file with
                 "--numouse", so no separate script is needed.
  * Add App    : add any .exe to the Hub (Steam-library style)

Requires: Python 3.8+, Pillow (OpenImage), pynput >= 1.7 (NuMouse).
Optional: pillow-heif (HEIC/HEIF/AVIF).

Run:   python UltimateHub.py
"""
import base64
import io
import itertools
import json
import math
import os
import secrets
import struct
import subprocess
import sys
import time
import traceback
import uuid
import zlib
from datetime import datetime, timedelta
from fractions import Fraction
from pathlib import Path
from threading import Event, Lock, Thread
import tkinter as tk
from tkinter import filedialog, ttk
from tkinter import font as tkfont

try:
    from PIL import Image, ImageCms, ImageSequence
    PIL_ERROR = None
except ImportError as _exc:                      # OpenImage then shows a hint
    Image = ImageCms = ImageSequence = None
    PIL_ERROR = str(_exc)

pillow_heif = None
if Image is not None:
    try:
        import pillow_heif
        pillow_heif.register_heif_opener()
        if hasattr(pillow_heif, "register_avif_opener"):
            try:
                pillow_heif.register_avif_opener()
            except Exception:
                pass
    except ImportError:
        pillow_heif = None

APP_NAME = "UltimateHub"
IS_WINDOWS = os.name == "nt"
FROZEN = bool(getattr(sys, "frozen", False))

if FROZEN:                                       # e.g. PyInstaller build
    SELF_PATH = Path(sys.executable).resolve()
    SELF_CMD = [str(SELF_PATH)]
else:
    SELF_PATH = Path(__file__).resolve()
    SELF_CMD = [sys.executable, "-u", str(SELF_PATH)]

BASE_DIR = SELF_PATH.parent
DATA_DIR = BASE_DIR / "hub_data"                 # added apps, icons, logs
ICON_DIR = DATA_DIR / "icons"
APPS_FILE = DATA_DIR / "apps.json"
NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0) if IS_WINDOWS else 0

# Set to False to use the normal Windows title bar (the Aero look then only
# applies inside the window). Handy if the custom frame ever misbehaves.
USE_AERO_FRAME = True


# ===========================================================================
#  SECTION 1 - RANDOM PHONE EXIF
#  30 real phone / tablet models with plausible camera data. Everything that
#  gets written is generated so that the numbers agree with each other
#  (exposure time, ISO, aperture, brightness, dates, software version...).
# ===========================================================================

LOOKBACK_YEARS = 3          # random capture dates fall in the last N years

# Apple iOS releases (version, release date). Used to pick a software version
# that actually existed on the capture date and runs on the chosen iPhone.
IOS_RELEASES = [
    ("10.0.2", (2016, 9, 23)), ("10.2", (2016, 12, 12)), ("10.3.3", (2017, 7, 19)),
    ("11.0.3", (2017, 10, 11)), ("11.2.5", (2018, 1, 23)), ("11.4.1", (2018, 7, 9)),
    ("12.0.1", (2018, 10, 8)), ("12.1.4", (2019, 2, 7)), ("12.4.1", (2019, 8, 26)),
    ("13.1.2", (2019, 9, 30)), ("13.3", (2019, 12, 10)), ("13.5.1", (2020, 6, 1)),
    ("13.7", (2020, 9, 1)),
    ("14.0.1", (2020, 9, 24)), ("14.2", (2020, 11, 5)), ("14.4.2", (2021, 3, 26)),
    ("14.8", (2021, 9, 13)),
    ("15.0.2", (2021, 10, 11)), ("15.2.1", (2022, 1, 26)), ("15.5", (2022, 5, 16)),
    ("15.7.9", (2023, 7, 24)), ("15.8.3", (2024, 7, 29)),
    ("16.0.2", (2022, 10, 10)), ("16.2", (2022, 12, 13)), ("16.4.1", (2023, 4, 7)),
    ("16.5.1", (2023, 6, 21)),
    ("17.0.3", (2023, 10, 4)), ("17.1.2", (2023, 11, 30)), ("17.2.1", (2024, 1, 2)),
    ("17.3.1", (2024, 2, 8)), ("17.4.1", (2024, 3, 21)), ("17.5.1", (2024, 5, 20)),
    ("17.6.1", (2024, 8, 7)),
    ("18.0.1", (2024, 9, 30)), ("18.1.1", (2024, 12, 3)), ("18.3.1", (2025, 2, 10)),
    ("18.4.1", (2025, 4, 16)), ("18.5", (2025, 5, 12)), ("18.6.2", (2025, 8, 20)),
    ("26.0.1", (2025, 9, 29)), ("26.1", (2025, 11, 3)), ("26.2", (2025, 12, 12)),
    ("26.3", (2026, 2, 11)), ("26.4", (2026, 3, 25)),
]
IOS_MAJOR_RELEASE = {
    10: (2016, 9, 13), 11: (2017, 9, 19), 12: (2018, 9, 17), 13: (2019, 9, 19),
    14: (2020, 9, 16), 15: (2021, 9, 20), 16: (2022, 9, 12), 17: (2023, 9, 18),
    18: (2024, 9, 16), 26: (2025, 9, 15),
}
IOS_NEXT_MAJOR = {10: 11, 11: 12, 12: 13, 13: 14, 14: 15, 15: 16, 16: 17, 17: 18, 18: 26}

ISO_STEPS = [20, 25, 32, 40, 50, 64, 80, 100, 125, 160, 200, 250, 320, 400, 500,
             640, 800, 1000, 1250, 1600, 2000, 2500, 3200, 4000, 5000, 6400]

TZ_OFFSETS = ["+03:00", "+03:00", "+01:00", "+02:00", "+00:00", "+01:00", "+02:00",
              "-05:00", "-08:00", "+05:30", "+08:00", "+09:00", "-03:00", "+04:00"]


def _phone(label, make, model, vendor, released, focal, eq35, fnum, iso, **extra):
    data = dict(label=label, make=make, model=model, vendor=vendor,
                released=released, focal=focal, eq35=eq35, fnum=fnum, iso=iso,
                iso_style="steps", byteorder="II", lens=False, flash=0,
                metering=2, program=2, exif_version=b"0220", offset_time=False,
                tablet=False)
    data.update(extra)
    return data


def _apple(label, model, released, focal, eq35, fnum, iso, ios):
    return _phone(label, "Apple", model, "apple", released, focal, eq35, fnum, iso,
                  byteorder="MM", lens=True, flash=16, metering=5, program=2,
                  exif_version=b"0232", offset_time=True, ios=ios)


def _samsung(label, model, released, focal, eq35, fnum, iso, fw, updates, **extra):
    return _phone(label, "samsung", model, "samsung", released, focal, eq35, fnum, iso,
                  fw=fw, updates=updates, **extra)


def _android(label, make, model, released, focal, eq35, fnum, iso, **extra):
    base = dict(vendor="android", flash=16, iso_style="free")
    base.update(extra)
    vendor = base.pop("vendor")
    return _phone(label, make, model, vendor, released, focal, eq35, fnum, iso, **base)


PHONES = [
    # ---- Apple (7) -------------------------------------------------------
    _apple("Apple iPhone 15", "iPhone 15", (2023, 9), 6.765, 24, 1.6, (32, 3200), (17, 26)),
    _apple("Apple iPhone 14", "iPhone 14", (2022, 9), 5.7, 26, 1.5, (32, 3200), (16, 26)),
    _apple("Apple iPhone 13", "iPhone 13", (2021, 9), 5.1, 26, 1.6, (32, 2500), (15, 26)),
    _apple("Apple iPhone 12", "iPhone 12", (2020, 10), 4.2, 26, 1.6, (32, 2500), (14, 26)),
    _apple("Apple iPhone 11", "iPhone 11", (2019, 9), 4.25, 26, 1.8, (32, 2000), (13, 26)),
    _apple("Apple iPhone XR", "iPhone XR", (2018, 10), 4.25, 26, 1.8, (25, 2000), (12, 18)),
    _apple("Apple iPhone 7", "iPhone 7", (2016, 9), 3.99, 28, 1.8, (20, 1600), (10, 15)),
    # ---- Samsung (9) -----------------------------------------------------
    _samsung("Samsung Galaxy S24", "SM-S921B", (2024, 1), 6.3, 24, 1.8, (50, 3200),
             "S921B", 6, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy S23", "SM-S911B", (2023, 2), 6.3, 24, 1.8, (50, 3200),
             "S911B", 5, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy S21", "SM-G991B", (2021, 1), 5.4, 26, 1.8, (50, 3200),
             "G991B", 4, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy A54 5G", "SM-A546B", (2023, 3), 6.2, 26, 1.8, (25, 3200),
             "A546B", 4, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy A52", "SM-A525F", (2021, 3), 5.2, 26, 1.8, (25, 3200),
             "A525F", 3, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy A14", "SM-A145F", (2023, 1), 3.6, 26, 1.8, (50, 1600),
             "A145F", 2, exif_version=b"0231", offset_time=True),
    _samsung("Samsung Galaxy A21s", "SM-A217F", (2020, 6), 4.6, 26, 2.0, (20, 2000),
             "A217F", 2),
    _samsung("Samsung Galaxy A12", "SM-A125F", (2020, 11), 4.6, 26, 2.0, (20, 1600),
             "A125F", 2),
    _samsung("Samsung Galaxy Tab S6 Lite", "SM-P610", (2020, 4), 3.4, 32, 2.0, (40, 1250),
             "P610", 3, tablet=True),
    # ---- Xiaomi family (6) -----------------------------------------------
    _android("Xiaomi Redmi Note 7", "Xiaomi", "Redmi Note 7", (2019, 2), 4.7, 26, 1.8, (98, 1600)),
    _android("Xiaomi Redmi Note 9", "Xiaomi", "M2003J15SG", (2020, 4), 4.7, 26, 1.79, (100, 1600)),
    _android("Xiaomi Redmi Note 11", "Xiaomi", "2201117TG", (2022, 1), 3.6, 26, 1.8, (100, 3200),
             exif_version=b"0231", offset_time=True),
    _android("Xiaomi Redmi Note 12", "Xiaomi", "23021RAAEG", (2023, 4), 3.6, 26, 1.8, (100, 3200),
             exif_version=b"0231", offset_time=True),
    _android("POCO X3 Pro", "Xiaomi", "M2102J20SG", (2021, 3), 4.7, 26, 1.79, (100, 3200),
             exif_version=b"0231"),
    _android("Xiaomi Redmi 9A", "Xiaomi", "M2006C3LG", (2020, 6), 3.6, 28, 2.2, (100, 1600)),
    # ---- Google (2) ------------------------------------------------------
    _android("Google Pixel 7", "Google", "Pixel 7", (2022, 10), 6.81, 24, 1.85, (40, 1600),
             byteorder="MM", lens=True, exif_version=b"0232", offset_time=True),
    _android("Google Pixel 8", "Google", "Pixel 8", (2023, 10), 6.81, 24, 1.68, (40, 1600),
             byteorder="MM", lens=True, exif_version=b"0232", offset_time=True),
    # ---- Others (6) ------------------------------------------------------
    _android("Huawei P30 lite", "HUAWEI", "MAR-LX1A", (2019, 4), 3.4, 26, 1.8, (50, 3200)),
    _android("realme 8", "realme", "RMX3085", (2021, 3), 5.5, 26, 1.8, (100, 3200),
             exif_version=b"0231"),
    _android("vivo Y20", "vivo", "V2027", (2020, 8), 3.6, 28, 2.2, (100, 1600)),
    _android("OnePlus Nord", "OnePlus", "AC2003", (2020, 7), 4.7, 26, 1.75, (100, 3200),
             exif_version=b"0231"),
    _android("OPPO A54", "OPPO", "CPH2239", (2021, 3), 3.5, 27, 2.2, (100, 1600)),
    _android("Motorola moto g(30)", "motorola", "moto g(30)", (2021, 3), 5.6, 26, 1.7, (100, 3200),
             exif_version=b"0231"),
]
assert len(PHONES) == 30


# --------------------------- TIFF / EXIF writer ----------------------------

def _enc_value(bo, typ, value):
    if typ == 2:                                    # ASCII (NUL terminated)
        data = str(value).encode("ascii", "replace") + b"\x00"
        return data, len(data)
    if typ == 7:                                    # UNDEFINED
        data = bytes(value)
        return data, len(data)
    if typ == 1:                                    # BYTE
        data = bytes(value if isinstance(value, (list, tuple)) else [value])
        return data, len(data)
    values = value if isinstance(value, list) else [value]
    if typ == 3:
        return b"".join(struct.pack(bo + "H", v) for v in values), len(values)
    if typ == 4:
        return b"".join(struct.pack(bo + "I", v) for v in values), len(values)
    if typ == 5:
        return b"".join(struct.pack(bo + "II", n, d) for n, d in values), len(values)
    if typ == 10:
        return b"".join(struct.pack(bo + "ii", n, d) for n, d in values), len(values)
    raise ValueError(f"unsupported EXIF type {typ}")


def _ifd_bytes(entries, offset, bo, next_ifd):
    entries = sorted(entries, key=lambda item: item[0])
    data_start = offset + 2 + 12 * len(entries) + 4
    body = bytearray()
    data = bytearray()
    for tag, typ, value in entries:
        payload, count = _enc_value(bo, typ, value)
        if len(payload) <= 4:
            field = payload.ljust(4, b"\x00")
        else:
            if len(data) % 2:
                data.append(0)
            field = struct.pack(bo + "I", data_start + len(data))
            data.extend(payload)
        body += struct.pack(bo + "HHI", tag, typ, count) + field
    if len(data) % 2:
        data.append(0)
    return (struct.pack(bo + "H", len(entries)) + bytes(body)
            + struct.pack(bo + "I", next_ifd) + bytes(data))


def build_tiff(byteorder, ifd0, exif_ifd, thumb=None, gps_ifd=None):
    """Return EXIF as raw TIFF bytes (IFD0 + Exif IFD + optional GPS IFD + thumbnail)."""
    bo = "<" if byteorder == "II" else ">"
    header = (b"II*\x00" if byteorder == "II" else b"MM\x00*") + struct.pack(bo + "I", 8)
    thumb_entries = []
    if thumb:
        thumb_entries = [
            (0x0103, 3, 6), (0x011A, 5, (72, 1)), (0x011B, 5, (72, 1)),
            (0x0128, 3, 2), (0x0201, 4, 0), (0x0202, 4, len(thumb)),
        ]

    # Pass 1: measure (sizes do not depend on the pointer values).
    pointers = [(0x8769, 4, 0)] + ([(0x8825, 4, 0)] if gps_ifd else [])
    len0 = len(_ifd_bytes(ifd0 + pointers, 8, bo, 0))
    off_exif = 8 + len0
    len_exif = len(_ifd_bytes(exif_ifd, off_exif, bo, 0))
    off_gps = off_exif + len_exif
    len_gps = len(_ifd_bytes(gps_ifd, off_gps, bo, 0)) if gps_ifd else 0
    off1 = off_gps + len_gps
    off_thumb = off1
    if thumb:
        off_thumb = off1 + len(_ifd_bytes(thumb_entries, off1, bo, 0))

    # Pass 2: real offsets.
    out = bytearray(header)
    real0 = ifd0 + [(0x8769, 4, off_exif)] + ([(0x8825, 4, off_gps)] if gps_ifd else [])
    out += _ifd_bytes(real0, 8, bo, off1 if thumb else 0)
    out += _ifd_bytes(exif_ifd, off_exif, bo, 0)
    if gps_ifd:
        out += _ifd_bytes(gps_ifd, off_gps, bo, 0)
    if thumb:
        entries = [(0x0201, 4, off_thumb) if e[0] == 0x0201 else e for e in thumb_entries]
        out += _ifd_bytes(entries, off1, bo, 0)
        out += thumb
    return bytes(out)


def exif_app1_segment(tiff: bytes) -> bytes:
    """JPEG APP1 segment (FF E1 ...) holding the EXIF block."""
    payload = b"Exif\x00\x00" + tiff
    if len(payload) + 2 > 0xFFFF:
        raise ValueError("EXIF block too large for a JPEG segment")
    return b"\xff\xe1" + struct.pack(">H", len(payload) + 2) + payload


def make_thumbnail(image) -> bytes:
    """
    Small JPEG preview (like real phones embed), made from the clean pixels.
    The pixels are detached from the source image first: Pillow would
    otherwise copy the source's comment / profile into the thumbnail.
    """
    thumb = image.convert("RGB") if image.mode not in ("RGB", "L") else image.copy()
    thumb.thumbnail((160, 120))
    thumb = Image.frombytes(thumb.mode, thumb.size, thumb.tobytes())
    buffer = io.BytesIO()
    thumb.save(buffer, format="JPEG", quality=80, comment=b"")
    return buffer.getvalue()


# ------------------------------ generator ----------------------------------

def _rat(value, limit=1_000_000):
    f = Fraction(value).limit_denominator(limit)
    return (f.numerator, f.denominator)


def _srat(value, den=1_000_000):
    return (int(round(value * den)), den)


def _ascii_time(dt):
    return dt.strftime("%Y:%m:%d %H:%M:%S")


def _month_letter(month):
    return chr(ord("A") + month - 1)


def _year_letter(year):
    return chr(ord("A") + year - 2001)


class ExifResult:
    """The generated EXIF block plus a human readable summary."""

    def __init__(self, tiff, summary, phone, when, iso, exposure, fnum, software, location=None):
        self.location = location            # (lat, lon) or None
        self.tiff = tiff
        self.summary = summary
        self.phone = phone
        self.when = when
        self.iso = iso
        self.exposure = exposure
        self.fnum = fnum
        self.software = software


def pick_phone(rng=None, exclude_vendors=()):
    """A random phone, optionally leaving out some vendors (e.g. "apple")."""
    rng = rng or secrets.SystemRandom()
    pool = [p for p in PHONES if p["vendor"] not in exclude_vendors] or PHONES
    return rng.choice(pool)


def _capture_window(phone, rng, now):
    """Returns (datetime, software_or_None) consistent with the phone."""
    released = datetime(phone["released"][0], phone["released"][1], 1) + timedelta(days=45)
    low = max(released, now - timedelta(days=365 * LOOKBACK_YEARS))
    high = now - timedelta(hours=2)
    if low >= high:
        low = high - timedelta(days=30)

    windows = []                                     # (start, end, software)
    if phone["vendor"] == "apple":
        lo_major, hi_major = phone["ios"]
        valid = []
        for version, (y, m, d) in IOS_RELEASES:
            major = int(version.split(".")[0])
            if not lo_major <= major <= hi_major:
                continue
            date = datetime(y, m, d)
            nxt = IOS_NEXT_MAJOR.get(major)
            if major < hi_major and nxt and date >= datetime(*IOS_MAJOR_RELEASE[nxt]):
                continue        # the device would already be on a newer major
            valid.append((date, version))
        valid.sort()
        for index, (date, version) in enumerate(valid):
            end = valid[index + 1][0] if index + 1 < len(valid) else high
            start = max(date, low)
            end = min(end, high)
            if start < end:
                windows.append((start, end, version))
    if not windows:
        windows = [(low, high, None)]

    weights = [(end - start).total_seconds() for start, end, _ in windows]
    start, end, software = rng.choices(windows, weights=weights, k=1)[0]
    span = (end - start).total_seconds()
    day = start + timedelta(seconds=rng.random() * span)

    hours = list(range(7, 24))
    hour_weights = [1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1]
    hour = rng.choices(hours, weights=hour_weights, k=1)[0]
    when = day.replace(hour=hour, minute=rng.randint(0, 59), second=rng.randint(0, 59),
                       microsecond=rng.randint(0, 999_999))
    if when > high:
        when = high - timedelta(minutes=rng.randint(1, 600))
    if when < start:
        when = start
    return when, software


def _scene_ev(hour, rng):
    """EV at ISO 100 for a typical scene at that time of day."""
    if 10 <= hour < 16:
        kind = rng.choices(["sun", "cloud", "indoor"], weights=[45, 20, 35])[0]
    elif 7 <= hour < 10 or 16 <= hour < 19:
        kind = rng.choices(["low_sun", "shade", "indoor"], weights=[30, 30, 40])[0]
    else:
        kind = rng.choices(["indoor_dim", "night"], weights=[60, 40])[0]
    base = {"sun": (14.2, 0.6), "cloud": (12.3, 0.6), "indoor": (8.0, 1.2),
            "low_sun": (12.0, 0.8), "shade": (10.6, 0.8),
            "indoor_dim": (6.0, 1.3), "night": (3.0, 1.4)}[kind]
    return rng.gauss(*base)


def _exposure(phone, ev100, rng):
    """Pick ISO / shutter like a phone's auto exposure would."""
    n = phone["fnum"]
    iso_min, iso_max = phone["iso"]
    t_slow = 1 / 30.0              # handheld limit before the phone raises ISO
    t_floor = 1 / 4.0              # longest exposure we ever write
    t_fast = 1 / 8000.0

    t = n * n * 100.0 / (iso_min * 2.0 ** ev100)
    iso = float(iso_min)
    if t > t_slow:
        iso = min(iso_max, n * n * 100.0 / (t_slow * 2.0 ** ev100))
        iso = max(iso, iso_min)
    if phone["iso_style"] == "steps":
        allowed = [s for s in ISO_STEPS if iso_min <= s <= iso_max]
        iso = min(allowed, key=lambda s: abs(math.log2(s) - math.log2(iso)))
    else:
        iso = int(round(iso))
    t = n * n * 100.0 / (iso * 2.0 ** ev100)
    t = min(max(t, t_fast), t_floor)
    return int(iso), t


def build_phone_exif(phone, width, height, orientation=1, color_space=1,
                     thumbnail=None, rng=None, now=None, location=None):
    """Generate a complete, self-consistent EXIF block for `phone`.
    `location` is an optional (lat, lon): the GPS block and the time zone follow it."""
    rng = rng or secrets.SystemRandom()
    now = now or datetime.now()

    when, software = _capture_window(phone, rng, now)
    vendor = phone["vendor"]
    if vendor == "samsung":
        years = max(0, min(when.year - phone["released"][0], phone["updates"]))
        software = "{}XX{}{}{}{}{}{}".format(
            phone["fw"], rng.choice("US"), rng.randint(1, 9), chr(ord("A") + years),
            _year_letter(when.year), _month_letter(when.month), rng.randint(1, 9))

    iso, t = _exposure(phone, _scene_ev(when.hour, rng), rng)
    n = phone["fnum"]
    exposure_den = max(1, int(round(1.0 / t))) if t < 1 else 1
    exposure = (1, exposure_den) if t < 0.95 else (int(round(t * 10)), 10)
    t_real = exposure[0] / exposure[1]

    av = 2.0 * math.log2(n)
    tv = -math.log2(t_real)
    sv = math.log2(iso / 3.125)
    bv = av + tv - sv

    dt_text = _ascii_time(when)
    sub = "{:03d}".format(when.microsecond // 1000)
    gps = None
    if location:
        lat, lon = location
        offset_minutes = tz_offset_minutes(lat, lon, when)      # time zone of the place
        offset = format_offset(offset_minutes)
        utc = when - timedelta(minutes=offset_minutes)
        altitude = min(4200.0, rng.lognormvariate(math.log(90.0), 1.1))
        gps = build_gps_ifd(lat, lon, altitude, utc, vendor, rng)
    else:
        offset = rng.choice(TZ_OFFSETS)
    focal = phone["focal"]

    ifd0 = [
        (0x010F, 2, phone["make"]), (0x0110, 2, phone["model"]),
        (0x0112, 3, orientation), (0x011A, 5, (72, 1)), (0x011B, 5, (72, 1)),
        (0x0128, 3, 2), (0x0132, 2, dt_text), (0x0213, 3, 1),
    ]
    if software:
        ifd0.append((0x0131, 2, software))
    if vendor == "apple" and int(software.split(".")[0]) >= 15:
        ifd0.append((0x013C, 2, phone["model"]))     # HostComputer (iOS 15+)

    ex = [
        (0x829A, 5, exposure), (0x829D, 5, _rat(n, 1000)),
        (0x8822, 3, phone["program"]), (0x8827, 3, iso),
        (0x9000, 7, phone["exif_version"]),
        (0x9003, 2, dt_text), (0x9004, 2, dt_text),
        (0x9101, 7, b"\x01\x02\x03\x00"),
        (0x9201, 10, _srat(tv)), (0x9202, 5, _srat(av)), (0x9203, 10, _srat(bv)),
        (0x9204, 10, (0, 1)), (0x9207, 3, phone["metering"]),
        (0x9209, 3, phone["flash"]), (0x920A, 5, _rat(focal, 1000)),
        (0x9290, 2, sub), (0x9291, 2, sub), (0x9292, 2, sub),
        (0xA000, 7, b"0100"), (0xA001, 3, color_space),
        (0xA002, 4, int(width)), (0xA003, 4, int(height)),
        (0xA402, 3, 0), (0xA403, 3, 0), (0xA405, 3, int(phone["eq35"])),
        (0xA406, 3, 0),
    ]
    if phone["offset_time"]:
        ex += [(0x9010, 2, offset), (0x9011, 2, offset), (0x9012, 2, offset)]
    if vendor != "apple":
        ex += [(0x9205, 5, _srat(av)), (0xA404, 5, (1, 1))]
    if vendor == "apple":
        cx = int(width * rng.uniform(0.42, 0.58))
        cy = int(height * rng.uniform(0.42, 0.58))
        ex += [(0x9214, 3, [cx, cy, int(width * 0.55), int(height * 0.44)]),
               (0xA217, 3, 2)]
    if vendor == "samsung":
        unique = "{}{:02d}{}{}{:02d}{}".format(
            rng.choice("CDFGHJKLMNPRSTW"), rng.randint(10, 14),
            "".join(rng.choice("ABCDEFGHJKLMNPQRSTUVWXYZ") for _ in range(3)),
            rng.choice("AB"), rng.randint(0, 3),
            "".join(rng.choice("ABCDEFGHJKLMNPQRSTUVWXYZ") for _ in range(2)))
        ex.append((0xA420, 2, unique))
    if phone["lens"]:
        side = "back camera"
        lens = "{} {} {}mm f/{}".format(phone["model"], side, ("%g" % focal), ("%g" % n))
        ex += [(0xA432, 5, [_rat(focal, 1000), _rat(focal, 1000), _rat(n, 1000), _rat(n, 1000)]),
               (0xA433, 2, phone["make"]), (0xA434, 2, lens)]

    tiff = build_tiff(phone["byteorder"], ifd0, ex, thumbnail, gps)
    shutter = "1/%d s" % exposure[1] if exposure[0] == 1 else "%g s" % t_real
    summary = "{}{}  |  {:%Y-%m-%d %H:%M}  |  ISO {}  |  f/{:g}  |  {}".format(
        phone["label"], "  (" + (software or "") + ")" if software else "",
        when, iso, n, shutter)
    return ExifResult(tiff, summary, phone, when, iso, exposure, n, software, location)


# ===========================================================================
#  SECTION 1b - RANDOM LOCATION (always on land) + TIME ZONE + GPS BLOCK
#  The land mask (0.1 degree cells; sea, big lakes, polar caps removed) and a
#  population weight grid are embedded at the end of this file.
# ===========================================================================

_GEO = {}


def _land_mask():
    mask = _GEO.get("mask")
    if mask is None:
        mask = _GEO["mask"] = zlib.decompress(base64.b64decode(LAND_MASK_B64))
    return mask


def is_usable_land(lat, lon):
    """True if (lat, lon) lies on land (not sea, big lake, Antarctica, ice cap)."""
    row = int((lat + 90.0) / 0.1)
    col = int((lon + 180.0) / 0.1)
    if not (0 <= row < 1800 and 0 <= col < 3600):
        return False
    return bool((_land_mask()[row * 450 + (col >> 3)] >> (7 - (col & 7))) & 1)


def _populated_cells():
    cells = _GEO.get("cells")
    if cells is None:
        grid = zlib.decompress(base64.b64decode(POP_GRID_B64))
        found, weights = [], []
        for index, q in enumerate(grid):
            if q:
                found.append(index)
                weights.append(math.exp(q / 20.0) - 1.0)
        cells = _GEO["cells"] = (found, list(itertools.accumulate(weights)))
    return cells


def random_land_point(rng=None, populated_share=0.70):
    """
    A random (lat, lon) on land. 70 % of the time near inhabited areas (picked by
    population, then a random spot inside a 50 km cell), 30 % anywhere on land.
    Every land coordinate is possible; the sea never is.
    """
    rng = rng or secrets.SystemRandom()
    found, cumulative = _populated_cells()
    for attempt in range(2000):
        if attempt < 400 and rng.random() < populated_share:
            index = rng.choices(found, cum_weights=cumulative, k=1)[0]
            row, col = divmod(index, 720)
            lat = -90.0 + (row + rng.random()) * 0.5
            lon = -180.0 + (col + rng.random()) * 0.5
        else:
            lat = math.degrees(math.asin(rng.uniform(-1.0, 1.0)))
            lon = rng.uniform(-180.0, 180.0)
        if is_usable_land(lat, lon):
            return round(lat, 6), round(lon, 6)
    raise RuntimeError("could not find a land point")


# (lat_min, lat_max, lon_min, lon_max, standard offset in minutes or None = from the
#  longitude, daylight-saving rule). First match wins. Good approximations of the
#  real time zones, not a full tz database.
TZ_REGIONS = [
    (36.0, 42.2, 26.0, 44.8, 180, None),        # Turkey
    (38.5, 43.6, 40.0, 50.5, 240, None),        # Caucasus
    (16.0, 26.5, 51.5, 59.9, 240, None),        # UAE, Oman
    (25.0, 39.8, 44.0, 63.4, 210, None),        # Iran
    (29.4, 38.5, 60.5, 74.9, 270, None),        # Afghanistan
    (23.6, 37.0, 60.9, 77.0, 300, None),        # Pakistan
    (26.3, 30.5, 80.0, 88.2, 345, None),        # Nepal
    (5.5, 37.0, 68.0, 89.0, 330, None),         # India, Sri Lanka
    (20.7, 26.7, 88.1, 92.7, 360, None),        # Bangladesh, Bhutan
    (9.5, 28.5, 92.2, 98.0, 390, None),         # Myanmar
    (20.0, 24.0, 98.0, 101.2, 390, None),       # Myanmar (Shan)
    (0.8, 7.4, 99.6, 119.3, 480, None),         # Malaysia, Singapore, Brunei
    (4.5, 21.0, 116.0, 127.0, 480, None),       # Philippines
    (30.0, 46.0, 124.0, 146.0, 540, None),      # Korea, Japan
    (18.0, 53.6, 73.5, 135.0, 480, None),       # China, Mongolia, Taiwan
    (-36.0, -13.5, 112.9, 129.0, 480, None),    # Western Australia
    (-39.0, -10.5, 129.0, 141.0, 570, None),    # Central Australia
    (-44.0, -9.0, 141.0, 154.0, 600, None),     # Eastern Australia
    (-47.5, -34.0, 166.0, 178.6, 720, None),    # New Zealand
    (51.0, 72.0, -170.0, -130.0, -540, "US"),   # Alaska
    (18.5, 22.5, -160.6, -154.5, -600, None),   # Hawaii
    (14.5, 24.0, -107.0, -86.7, -360, None),    # Mexico
    (24.5, 70.0, -170.0, -52.0, None, "US"),    # USA, Canada
    (-55.0, -21.8, -73.6, -53.6, -180, None),   # Argentina
    (-12.0, 15.0, 33.0, 48.0, 180, None),       # East Africa
    (-18.0, -4.4, 11.7, 24.0, 60, None),        # Angola
    (-35.0, -8.0, 11.5, 42.0, 120, None),       # Southern Africa
    (27.6, 36.0, -13.2, -1.0, 60, None),        # Morocco
    (19.0, 37.5, -8.7, 12.0, 60, None),         # Algeria, Tunisia
    (4.0, 25.0, -17.6, 3.0, 0, None),           # West Africa
    (2.0, 24.0, 3.0, 16.0, 60, None),           # Nigeria, Niger, Cameroon
    (22.0, 37.0, 24.5, 36.0, 120, None),        # Egypt, Libya, Levant
    (12.0, 37.5, 36.0, 55.0, 180, None),        # Arabia, Iraq
    (44.0, 51.5, 22.0, 40.3, 120, "EU"),        # Ukraine
    (51.0, 56.2, 23.2, 32.8, 180, None),        # Belarus
    (50.0, 70.0, 27.5, 60.0, 180, None),        # Western Russia
    (49.0, 54.9, 20.0, 24.2, 60, "EU"),         # Eastern Poland
    (34.5, 70.1, 20.0, 31.5, 120, "EU"),        # Eastern Europe, Finland, Baltics, Greece
    (63.0, 67.0, -25.0, -13.0, 0, None),        # Iceland
    (49.8, 61.0, -11.0, 2.0, 0, "EU"),          # UK, Ireland
    (36.8, 42.0, -9.6, -6.2, 0, "EU"),          # Portugal
    (35.5, 71.0, -9.6, 20.0, 60, "EU"),         # Central / Western Europe, Spain
]


def _nth_sunday(year, month, n):
    """n-th Sunday of a month (n = -1: the last one)."""
    if n > 0:
        first = datetime(year, month, 1)
        return first + timedelta(days=(6 - first.weekday()) % 7 + 7 * (n - 1))
    nxt = datetime(year + (month == 12), month % 12 + 1, 1)
    last = nxt - timedelta(days=1)
    return last - timedelta(days=(last.weekday() + 1) % 7)


def _dst_active(rule, when):
    day = datetime(when.year, when.month, when.day)
    if rule == "EU":
        return _nth_sunday(when.year, 3, -1) <= day < _nth_sunday(when.year, 10, -1)
    if rule == "US":
        return _nth_sunday(when.year, 3, 2) <= day < _nth_sunday(when.year, 11, 1)
    return False


def tz_offset_minutes(lat, lon, when):
    """UTC offset (minutes) at a place for a local date; DST for Europe / North America."""
    standard, rule = None, None
    for lat0, lat1, lon0, lon1, std, dst in TZ_REGIONS:
        if lat0 <= lat <= lat1 and lon0 <= lon <= lon1:
            standard, rule = std, dst
            break
    if standard is None:
        standard = int(math.floor(lon / 15.0 + 0.5)) * 60
        standard = max(-720, min(840, standard))
    if rule and _dst_active(rule, when):
        standard += 60
    return standard


def format_offset(minutes):
    sign = "+" if minutes >= 0 else "-"
    minutes = abs(minutes)
    return "%s%02d:%02d" % (sign, minutes // 60, minutes % 60)


def _dms(value):
    v = abs(value)
    degrees = int(v)
    minutes = int((v - degrees) * 60)
    seconds = round((v - degrees - minutes / 60.0) * 3600.0, 4)
    if seconds >= 60:
        seconds -= 60
        minutes += 1
    if minutes >= 60:
        minutes -= 60
        degrees += 1
    return [(degrees, 1), (minutes, 1), (int(round(seconds * 10000)), 10000)]


def build_gps_ifd(lat, lon, altitude, utc, vendor, rng):
    """EXIF GPS block like a phone writes it (position, altitude, UTC time)."""
    ifd = [
        (0x0000, 1, [2, 3, 0, 0] if vendor == "apple" else [2, 2, 0, 0]),
        (0x0001, 2, "N" if lat >= 0 else "S"), (0x0002, 5, _dms(lat)),
        (0x0003, 2, "E" if lon >= 0 else "W"), (0x0004, 5, _dms(lon)),
        (0x0005, 1, [0]), (0x0006, 5, (int(round(altitude * 100)), 100)),
        (0x0007, 5, [(utc.hour, 1), (utc.minute, 1), (utc.second, 1)]),
        (0x001D, 2, utc.strftime("%Y:%m:%d")),
    ]
    if vendor == "apple":
        ifd += [(0x000C, 2, "K"), (0x000D, 5, (0, 1)),
                (0x0010, 2, "T"), (0x0011, 5, (int(rng.uniform(0, 360) * 100), 100)),
                (0x001F, 5, (int(rng.uniform(3, 35) * 100), 100))]
    else:
        ifd.append((0x001B, 7, b"ASCII\x00\x00\x00GPS"))
    return ifd


def format_location(lat, lon):
    return "%.4f\u00b0 %s, %.4f\u00b0 %s" % (abs(lat), "N" if lat >= 0 else "S",
                                              abs(lon), "E" if lon >= 0 else "W")


# ===========================================================================
#  SECTION 2 - IMAGE ENGINE (OpenImage)
# ===========================================================================

QUALITY_HIGH = "High quality (95)"
QUALITY_MAX = "Maximum quality"

IMAGE_TYPES = (
    "*.jpg *.jpeg *.png *.webp *.tif *.tiff *.bmp *.gif *.ico "
    "*.ppm *.pgm *.pbm *.pnm *.tga *.heic *.heif *.avif"
)

# Format label -> (Pillow encoder name, extension)
CONVERSION_FORMATS = {
    "Original format": (None, None),
    "JPEG": ("JPEG", ".jpg"),
    "PNG": ("PNG", ".png"),
    "WebP": ("WEBP", ".webp"),
    "TIFF": ("TIFF", ".tiff"),
    "BMP": ("BMP", ".bmp"),
    "GIF": ("GIF", ".gif"),
    "HEIC / HEIF": ("HEIF", ".heic"),
    "AVIF": ("AVIF", ".avif"),
}

# Formats that can carry an EXIF block with this tool.
EXIF_FORMATS = ("JPEG", "PNG", "WEBP", "HEIF", "AVIF")


def desktop_path():
    path = Path.home() / "Desktop"
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError:
        return Path.home()
    return path


def random_filename(extension):
    return f"{secrets.randbelow(100_000_000):08d}{extension.lower()}"


def normalize_format(name):
    """Map Pillow / file-extension format names to the encoder names used here."""
    name = (name or "").upper()
    return {"JPG": "JPEG", "MPO": "JPEG", "TIF": "TIFF", "HEIC": "HEIF"}.get(name, name)


def detect_format(path):
    """Detect the real format from the file contents (not the extension)."""
    with Image.open(path) as im:
        return normalize_format(im.format or Path(path).suffix.lstrip("."))


def orientation_ops():
    T = Image.Transpose
    return {2: T.FLIP_LEFT_RIGHT, 3: T.ROTATE_180, 4: T.FLIP_TOP_BOTTOM,
            5: T.TRANSPOSE, 6: T.ROTATE_270, 7: T.TRANSVERSE, 8: T.ROTATE_90}


def safe_orientation(image):
    """EXIF orientation (1-8). Any problem reading it simply returns 1."""
    try:
        value = image.getexif().get(0x0112, 1)
        return value if value in range(1, 9) else 1
    except Exception:
        return 1


def apply_orientation(image, orientation):
    op = orientation_ops().get(orientation)
    return image.transpose(op) if op is not None else image


def icc_is_srgb(icc_profile):
    if not icc_profile:
        return True
    try:
        profile = ImageCms.ImageCmsProfile(io.BytesIO(icc_profile))
        return "srgb" in ImageCms.getProfileDescription(profile).lower()
    except Exception:
        return False


def convert_to_srgb(image, icc_profile):
    """
    The embedded ICC profile is dropped on export, so wide-gamut images are
    converted to sRGB first to keep their colours. Unchanged on any problem.
    """
    if not icc_profile or image.mode not in ("RGB", "RGBA") or icc_is_srgb(icc_profile):
        return image
    try:
        source = ImageCms.ImageCmsProfile(io.BytesIO(icc_profile))
        target = ImageCms.createProfile("sRGB")
        alpha = image.getchannel("A") if image.mode == "RGBA" else None
        rgb = image.convert("RGB") if alpha is not None else image
        converted = ImageCms.profileToProfile(rgb, source, target, outputMode="RGB")
        if converted is None:
            return image
        if alpha is not None:
            converted.putalpha(alpha)
        return converted
    except Exception:
        return image


def clean_pixels(frame):
    """Detach decoded pixels from source metadata and decoder-owned storage."""
    frame.load()
    if frame.mode in ("P", "PA"):
        # frombytes() would lose the palette, so expand to real colours.
        transparent = frame.mode == "PA" or "transparency" in frame.info
        frame = frame.convert("RGBA" if transparent else "RGB")
    return Image.frombytes(frame.mode, frame.size, frame.tobytes())


# ------------------- JPEG / PNG: lossless byte-level cleaning ---------------

def keep_jpeg_segment(marker, payload, keep_jfif=True):
    """
    Whitelist: only segments needed to decode / display the picture survive.
    Dropped: EXIF/XMP (APP1), MPF/FlashPix (APP2 non-ICC), IPTC/Photoshop
    (APP13), JUMBF/C2PA, vendor APPn and COM comments.
    """
    if 0xE0 <= marker <= 0xEF:
        if marker == 0xE0:
            return keep_jfif and payload.startswith(b"JFIF\x00")
        if marker == 0xE2:
            return payload.startswith(b"ICC_PROFILE\x00")
        if marker == 0xEE:
            return payload.startswith(b"Adobe")
        return False
    if marker == 0xFE:
        return False
    return True


def strip_jpeg_metadata(source, destination, exif_app1=None, keep_jfif=True):
    """
    Rewrite a JPEG without any metadata segments (optionally inserting a new
    EXIF segment right after SOI). Image scan data is copied byte-for-byte (no
    re-compression). Anything after the end-of-image marker (hidden trailers,
    embedded motion-photo videos...) is dropped too. The original EXIF is never
    parsed, so malformed EXIF cannot cause problems.
    """
    data = Path(source).read_bytes()
    if len(data) < 4 or data[:2] != b"\xff\xd8":
        raise ValueError("The file does not contain a valid JPEG start marker.")

    out = bytearray(b"\xff\xd8")
    if exif_app1:
        out.extend(exif_app1)
    i = 2
    n = len(data)

    while i < n:
        if data[i] != 0xFF:
            raise ValueError("Unexpected data found between JPEG segments.")
        while i < n and data[i] == 0xFF:
            i += 1
        if i >= n:
            break

        marker = data[i]
        i += 1

        if marker == 0xD9:  # End of image: everything after it is discarded.
            out.extend(b"\xff\xd9")
            break

        if marker == 0xD8 or 0xD0 <= marker <= 0xD7 or marker == 0x01:
            out.extend(bytes((0xFF, marker)))     # standalone markers
            continue

        if i + 2 > n:
            raise ValueError("The JPEG file is truncated before a segment length.")
        seg_len = int.from_bytes(data[i:i + 2], "big")
        if seg_len < 2 or i + seg_len > n:
            raise ValueError("The JPEG contains an invalid segment length.")

        segment_end = i + seg_len
        if keep_jpeg_segment(marker, data[i + 2:segment_end], keep_jfif):
            out.extend(bytes((0xFF, marker)))
            out.extend(data[i:segment_end])
        i = segment_end

        if marker == 0xDA:  # Start of scan: copy entropy-coded data.
            j = i
            while j < n - 1:
                nxt = data[j + 1]
                if (data[j] == 0xFF and nxt not in (0x00, 0xFF)
                        and not 0xD0 <= nxt <= 0xD7):
                    break  # next real marker
                j += 1
            else:
                j = n
            out.extend(data[i:j])
            i = j

    Path(destination).write_bytes(out)


def rotate_jpeg(source, destination, orientation):
    """
    The orientation tag disappears with the rest of the EXIF, so photos that
    relied on it would end up sideways. For those, the pixels are rotated
    upright and saved at high quality (the one case where a JPEG is re-encoded).
    """
    with Image.open(source) as original:
        icc = original.info.get("icc_profile")
        original.load()
        pixels = Image.frombytes(original.mode, original.size, original.tobytes())

    pixels = apply_orientation(pixels, orientation)
    if pixels.mode not in ("RGB", "L"):
        pixels = pixels.convert("RGB")
    options = {"format": "JPEG", "quality": 95, "subsampling": 0, "optimize": True}
    if icc:
        options["icc_profile"] = icc
    pixels.save(destination, **options)


PNG_KEEP = {
    b"IHDR", b"PLTE", b"IDAT", b"IEND", b"tRNS",                    # structure
    b"gAMA", b"cHRM", b"sRGB", b"iCCP", b"cICP", b"mDCV", b"cLLI",  # colour
    b"sBIT", b"bKGD", b"pHYs",
    b"acTL", b"fcTL", b"fdAT",                                       # APNG
}


def _png_chunk(kind, payload):
    return (struct.pack(">I", len(payload)) + kind + payload
            + struct.pack(">I", zlib.crc32(kind + payload) & 0xFFFFFFFF))


def strip_png_metadata(source, destination, exif_tiff=None):
    """Remove PNG text, EXIF, time and other ancillary chunks. Optionally
    inserts a new eXIf chunk (raw TIFF bytes) before the image data."""
    data = Path(source).read_bytes()
    signature = b"\x89PNG\r\n\x1a\n"
    if not data.startswith(signature):
        raise ValueError("The file does not contain a valid PNG signature.")

    out = bytearray(signature)
    inserted = exif_tiff is None
    i = len(signature)
    while i + 12 <= len(data):
        length = int.from_bytes(data[i:i + 4], "big")
        end = i + 12 + length
        if end > len(data):
            raise ValueError("The PNG contains a truncated chunk.")
        kind = data[i + 4:i + 8]
        critical = (kind[0] & 0x20) == 0  # uppercase first letter = critical
        if kind == b"IDAT" and not inserted:
            out.extend(_png_chunk(b"eXIf", exif_tiff))
            inserted = True
        if kind in PNG_KEEP or critical:
            out.extend(data[i:end])
        i = end
        if kind == b"IEND":
            break
    Path(destination).write_bytes(out)


# ------------------------------ conversion ----------------------------------

def downscale_size(width, height):
    """
    New size for "slightly reduce the resolution": the long edge drops to the
    next round hundred (4032 -> 4000, 4000 -> 3900) and the short edge follows,
    so the aspect ratio is kept and nothing is cropped. 3024 x 4032 becomes
    3000 x 4000. Returns None for images too small to bother with.
    """
    long_edge = max(width, height)
    if long_edge < 800:
        return None
    target = (long_edge // 100) * 100
    if target > long_edge * 0.995:
        target -= 100
    factor = target / long_edge
    return max(1, round(width * factor)), max(1, round(height * factor))


class RandomExif:
    """Request to write a random phone's EXIF into the exported image."""

    def __init__(self, rng=None, phone=None, downscale=False, location=False):
        self.rng = rng or secrets.SystemRandom()
        self.downscale = downscale       # also reduce the resolution a little
        # A random spot on land (GPS + matching time zone), or None.
        self.location = random_land_point(self.rng) if location else None
        # A reduced size such as 3000 x 4000 is not what an iPhone writes, so
        # in that mode only Android phones are picked.
        self.phone = phone or pick_phone(self.rng, ("apple",) if downscale else ())
        self.original_size = None
        self.resized = None              # (w, h) once the image was reduced
        self.result = None

    def make(self, width, height, orientation, color_space, thumb_image):
        thumb = make_thumbnail(thumb_image) if thumb_image is not None else None
        return self.build(width, height, orientation, color_space, thumb).tiff

    def build(self, width, height, orientation, color_space, thumbnail):
        self.result = build_phone_exif(self.phone, width, height, orientation, color_space,
                                       thumbnail, rng=self.rng, location=self.location)
        return self.result


def save_converted_image(source, destination, target_format, quality_mode, random_exif=None):
    """
    Re-encode image pixels in the selected format without carrying metadata
    (or with a random phone's EXIF). Returns a list of short notes about
    anything that could not be preserved.
    """
    Image.init()
    notes = []

    with Image.open(source) as original:
        source_format = normalize_format(original.format or Path(source).suffix.lstrip("."))
        fmt = target_format or source_format
        maximum = quality_mode == QUALITY_MAX
        frame_count = getattr(original, "n_frames", 1)
        animated_source = source_format in ("GIF", "WEBP", "PNG") and frame_count > 1

        if fmt not in Image.SAVE:
            hint = " Install it with: pip install pillow-heif" if fmt in ("HEIF", "AVIF") else ""
            raise ValueError(f"This Pillow installation cannot write {fmt} files.{hint}")

        # Animated output: keep every frame (EXIF is not written for these).
        if animated_source and fmt in ("GIF", "WEBP", "PNG"):
            frames, durations = [], []
            for frame in ImageSequence.Iterator(original):
                durations.append(frame.info.get("duration", 100))
                clean = clean_pixels(frame)
                if fmt == "GIF":
                    if clean.mode not in ("P", "L"):
                        clean = clean.convert("RGBA").quantize(
                            colors=256, method=Image.Quantize.FASTOCTREE)
                else:
                    clean = clean.convert("RGBA")
                frames.append(clean)
            if not frames:
                raise ValueError("No frames were found in the selected image.")
            common = dict(save_all=True, append_images=frames[1:], duration=durations,
                          loop=original.info.get("loop", 0))
            if fmt == "GIF":
                frames[0].save(destination, format="GIF", disposal=2, optimize=False, **common)
            elif fmt == "WEBP":
                frames[0].save(destination, format="WEBP", lossless=maximum,
                               quality=100 if maximum else 95, method=6, **common)
            else:
                frames[0].save(destination, format="PNG", **common)
            if random_exif is not None:
                random_exif.result = None
                notes.append("Animated images cannot carry random EXIF; saved without metadata.")
                if random_exif.downscale:
                    notes.append("Animated images are not resized.")
            return notes

        # Single image: first frame only.
        icc = original.info.get("icc_profile")
        clean = clean_pixels(original)
        if source_format not in ("HEIF", "AVIF"):  # pillow-heif already rotates
            clean = apply_orientation(clean, safe_orientation(original))
        clean = convert_to_srgb(clean, icc)
        if frame_count > 1:
            notes.append("Only the first frame / page was saved.")
        has_alpha_source = "transparency" in original.info

        if random_exif is not None and random_exif.downscale:
            random_exif.original_size = clean.size
            new_size = downscale_size(*clean.size)
            if new_size:
                clean = clean.resize(new_size, Image.LANCZOS)   # whole image, no cropping
                random_exif.resized = new_size
            else:
                notes.append("The image is too small to reduce its resolution.")

        exif_bytes = None
        if random_exif is not None:
            if fmt in EXIF_FORMATS:
                width, height = clean.size
                exif_bytes = random_exif.make(width, height, 1, 1, clean)
            else:
                random_exif.result = None
                notes.append(f"{fmt} files cannot store EXIF; saved without metadata.")

        if fmt == "JPEG":
            if clean.mode in ("RGBA", "LA") or has_alpha_source:
                rgba = clean.convert("RGBA")
                background = Image.new("RGB", rgba.size, (255, 255, 255))
                background.paste(rgba, mask=rgba.getchannel("A"))
                clean = background
            else:
                clean = clean.convert("RGB")
            clean.save(destination, format="JPEG", quality=100 if maximum else 95,
                       subsampling=0, optimize=True)
            if exif_bytes:
                # Pillow adds a JFIF header, which phone photos do not have. Put
                # the EXIF segment first and drop JFIF (lossless rewrite).
                strip_jpeg_metadata(destination, destination,
                                    exif_app1=exif_app1_segment(exif_bytes), keep_jfif=False)
        elif fmt == "PNG":
            if clean.mode not in ("1", "L", "LA", "P", "RGB", "RGBA", "I", "I;16"):
                clean = clean.convert("RGBA" if "A" in clean.getbands() else "RGB")
            options = dict(format="PNG", optimize=True)
            if exif_bytes:
                options["exif"] = exif_bytes
            clean.save(destination, **options)
        elif fmt == "WEBP":
            if clean.mode not in ("RGB", "RGBA"):
                clean = clean.convert("RGBA" if "A" in clean.getbands() else "RGB")
            options = dict(format="WEBP", lossless=maximum,
                           quality=100 if maximum else 95, method=6)
            if exif_bytes:
                options["exif"] = exif_bytes
            clean.save(destination, **options)
        elif fmt == "TIFF":
            clean.save(destination, format="TIFF", compression="tiff_lzw")
        elif fmt == "BMP":
            if clean.mode not in ("RGB", "RGBA"):
                clean = clean.convert("RGB")
            clean.save(destination, format="BMP")
        elif fmt == "GIF":
            if clean.mode not in ("P", "L"):
                clean = clean.convert("RGBA").quantize(
                    colors=256, method=Image.Quantize.FASTOCTREE)
            clean.save(destination, format="GIF", optimize=False)
        elif fmt in ("HEIF", "AVIF"):
            if clean.mode not in ("RGB", "RGBA"):
                clean = clean.convert("RGBA" if "A" in clean.getbands() else "RGB")
            options = dict(format=fmt, quality=100 if maximum else 95)
            if exif_bytes:
                options["exif"] = b"Exif\x00\x00" + exif_bytes
            clean.save(destination, **options)
        else:
            raise ValueError(f"Unsupported output format: {fmt}")
    return notes


def export_clean_image(source, destination, target_format, quality_mode, random_exif=None):
    """
    Write a metadata-free copy of `source` to `destination`.
      target_format  None = keep the original format
      random_exif    a RandomExif to write instead of leaving the file clean
    Returns (notes, random_exif_summary_or_None).
    """
    source = Path(source)
    destination = Path(destination)
    source_format = detect_format(source)
    keep_format = target_format is None or target_format == source_format
    resample = random_exif is not None and random_exif.downscale
    notes = []

    if keep_format and source_format == "JPEG" and not resample:
        if random_exif is None:
            with Image.open(source) as im:
                orientation = safe_orientation(im)
            if orientation == 1:
                strip_jpeg_metadata(source, destination)
            else:
                rotate_jpeg(source, destination, orientation)
                notes.append("The photo's rotation was applied to the pixels and it was "
                             "re-saved at quality 95.")
        else:
            # Lossless: pixels untouched, original orientation value kept.
            with Image.open(source) as im:
                orientation = safe_orientation(im)
                width, height = im.size
                icc = im.info.get("icc_profile")
                thumb = make_thumbnail(im)
            space = 1 if icc_is_srgb(icc) else 65535
            random_exif.build(width, height, orientation, space, thumb)
            strip_jpeg_metadata(source, destination,
                                exif_app1=exif_app1_segment(random_exif.result.tiff),
                                keep_jfif=False)
    elif keep_format and source_format == "PNG" and not resample:
        exif_tiff = None
        if random_exif is not None:
            with Image.open(source) as im:
                if getattr(im, "n_frames", 1) > 1:
                    notes.append("Animated images cannot carry random EXIF; saved without metadata.")
                    random_exif.result = None
                else:
                    orientation = safe_orientation(im)
                    width, height = im.size
                    thumb = make_thumbnail(im)
                    exif_tiff = random_exif.build(width, height, orientation, 1, thumb).tiff
        strip_png_metadata(source, destination, exif_tiff=exif_tiff)
    else:
        notes += save_converted_image(source, destination, target_format, quality_mode,
                                      random_exif)

    # Make sure the result can really be opened before it replaces anything.
    with Image.open(destination) as check:
        check.load()
    summary = random_exif.result.summary if (random_exif and random_exif.result) else None
    return notes, summary


# ===========================================================================
#  SECTION 3 - NUMOUSE (numpad mouse controller)
#  Started by the Hub as a background process:  UltimateHub.py --numouse --managed
#  In managed mode it exits cleanly on a "quit" line / when the Hub closes
#  its stdin pipe (for example if the Hub crashes), releasing held buttons.
# ===========================================================================

class NuMouseEngine:
    # Speeds are "pixels per 8 ms tick". Movement is time-based, so the real
    # speed is the same no matter how fast the loop actually runs.
    NORMAL_SPEED = 12
    SLOW_SPEED = 5
    ACCELERATION = 5.0
    DECELERATION = 80.0
    UPDATE_INTERVAL = 0.008
    STOP_THRESHOLD = 3.0
    SCROLL_AMOUNT = 2

    # Numpad "-" toggles control (virtual-key 109). The "-" on the main
    # keyboard row is NOT affected.
    TOGGLE_VK = 109

    # While control is ON the numpad keys NuMouse uses are blocked from
    # reaching other programs. Set SUPPRESS_TOGGLE_KEY to False if numpad "-"
    # should still type "-".
    SUPPRESS_USED_KEYS = True
    SUPPRESS_TOGGLE_KEY = True

    # Numpad virtual-key codes (NumLock ON) -> logical action.
    VK_MAP = {104: '8', 98: '2', 100: '4', 102: '6', 103: '7', 105: '9',
              101: '5', 96: '0', 99: '3', 110: ','}
    MOVE_KEYS = ('8', '2', '4', '6', '0')

    WM_KEYDOWN, WM_KEYUP, WM_SYSKEYDOWN, WM_SYSKEYUP = 0x0100, 0x0101, 0x0104, 0x0105

    def __init__(self, mouse, button_cls, listener_cls, managed=False):
        self.mouse = mouse
        self.Listener = listener_cls
        self.managed = managed
        self.button_map = {'7': button_cls.left, '9': button_cls.right,
                           '5': button_cls.middle}
        self.enabled = False
        self.active_keys = set()
        self.pressed_buttons = set()
        self.state_lock = Lock()
        self.velocity_x = 0.0
        self.velocity_y = 0.0
        self.listener = None
        self.shutdown_event = Event()
        self.swallowed_vks = set()      # keys whose key-down we blocked
        self.toggle_held = False        # ignores auto-repeat of the toggle key
        self._finalize_lock = Lock()
        self._finalized = False

    # ------------------------------------------------------------ helpers
    @staticmethod
    def get_vk(key):
        vk = getattr(key, 'vk', None)
        if vk is None:
            vk = getattr(getattr(key, 'value', None), 'vk', None)
        return vk

    def release_all_buttons(self):
        for button in list(self.pressed_buttons):
            try:
                self.mouse.release(button)
            except Exception:
                pass
        self.pressed_buttons.clear()

    # ----------------------------------------------------------- movement
    def movement_worker(self):
        last = time.perf_counter()
        acc_x = acc_y = 0.0
        while True:
            time.sleep(self.UPDATE_INTERVAL)
            now = time.perf_counter()
            dt = min(now - last, 0.05)          # real elapsed time
            last = now
            if dt <= 0:
                continue

            with self.state_lock:
                is_enabled = self.enabled
                keys = set(self.active_keys)

            target_x = target_y = 0.0
            if is_enabled:
                speed = self.SLOW_SPEED if '0' in keys else self.NORMAL_SPEED
                if '8' in keys:
                    target_y -= speed
                if '2' in keys:
                    target_y += speed
                if '4' in keys:
                    target_x -= speed
                if '6' in keys:
                    target_x += speed
                length = math.hypot(target_x, target_y)   # same speed diagonally
                if length > speed:
                    target_x = target_x / length * speed
                    target_y = target_y / length * speed

            if target_x != 0.0 or target_y != 0.0:
                blend = 1.0 - math.exp(-self.ACCELERATION * dt)
                self.velocity_x += (target_x - self.velocity_x) * blend
                self.velocity_y += (target_y - self.velocity_y) * blend
            else:
                damping = math.exp(-self.DECELERATION * dt)
                self.velocity_x *= damping
                self.velocity_y *= damping
                if math.hypot(self.velocity_x, self.velocity_y) < self.STOP_THRESHOLD:
                    self.velocity_x = self.velocity_y = 0.0

            if self.velocity_x == 0.0 and self.velocity_y == 0.0:
                acc_x = acc_y = 0.0
                continue

            # Keep the fractional part so slow movement stays smooth.
            scale = dt / self.UPDATE_INTERVAL
            acc_x += self.velocity_x * scale
            acc_y += self.velocity_y * scale
            step_x, step_y = int(acc_x), int(acc_y)
            if step_x or step_y:
                try:
                    self.mouse.move(step_x, step_y)
                except Exception:
                    pass
                acc_x -= step_x
                acc_y -= step_y

    # ------------------------------------------------------- key handling
    def handle_key_down(self, vk):
        """Process a key press. Returns True if the key should be blocked."""
        if vk == self.TOGGLE_VK:
            if self.toggle_held:
                return self.SUPPRESS_TOGGLE_KEY
            self.toggle_held = True
            with self.state_lock:
                self.enabled = not self.enabled
                self.active_keys.clear()
                if not self.enabled:
                    self.release_all_buttons()
                now_enabled = self.enabled
            print("\nMouse control " + ("ENABLED" if now_enabled else "DISABLED"), flush=True)
            if self.SUPPRESS_TOGGLE_KEY:
                self.swallowed_vks.add(vk)
            return self.SUPPRESS_TOGGLE_KEY

        action = self.VK_MAP.get(vk)
        if action is None:
            return False

        with self.state_lock:
            if not self.enabled:
                return False
            if action in self.MOVE_KEYS:
                self.active_keys.add(action)
            elif action in self.button_map:
                button = self.button_map[action]
                if button not in self.pressed_buttons:
                    self.mouse.press(button)
                    self.pressed_buttons.add(button)
            elif action == '3':
                self.mouse.scroll(0, self.SCROLL_AMOUNT)
            elif action == ',':
                self.mouse.scroll(0, -self.SCROLL_AMOUNT)

        if self.SUPPRESS_USED_KEYS:
            self.swallowed_vks.add(vk)
            return True
        return False

    def handle_key_up(self, vk):
        """Process a key release. Returns True if the key should be blocked."""
        if vk == self.TOGGLE_VK:
            self.toggle_held = False
        action = self.VK_MAP.get(vk)
        if action is not None:
            with self.state_lock:
                if action in self.MOVE_KEYS:
                    self.active_keys.discard(action)
                elif action in self.button_map:
                    button = self.button_map[action]
                    if button in self.pressed_buttons:
                        self.mouse.release(button)
                        self.pressed_buttons.discard(button)
        if vk in self.swallowed_vks:
            self.swallowed_vks.discard(vk)
            return True
        return False

    def win32_event_filter(self, msg, data):
        """Windows only: runs inside the keyboard hook, before other programs
        see the key. Everything is handled here so blocked keys are never
        processed twice."""
        swallow = False
        try:
            if msg in (self.WM_KEYDOWN, self.WM_SYSKEYDOWN):
                swallow = self.handle_key_down(data.vkCode)
            elif msg in (self.WM_KEYUP, self.WM_SYSKEYUP):
                swallow = self.handle_key_up(data.vkCode)
        except Exception:
            traceback.print_exc()
        if swallow:
            self.listener.suppress_event()      # raises; blocks the key system-wide
        return True

    def on_press(self, key):
        self.handle_key_down(self.get_vk(key))

    def on_release(self, key):
        self.handle_key_up(self.get_vk(key))

    # ----------------------------------------------------------- shutdown
    def finalize(self):
        """Release everything we hold. Safe to call more than once."""
        with self._finalize_lock:
            if self._finalized:
                return
            self._finalized = True
        with self.state_lock:
            self.enabled = False
            self.active_keys.clear()
            self.release_all_buttons()
        print("Controller stopped.", flush=True)

    def request_shutdown(self):
        self.shutdown_event.set()
        try:
            if self.listener is not None:
                self.listener.stop()
        except Exception:
            pass

    def watch_parent(self):
        """Managed mode: exit when the Hub sends "quit" or closes our stdin."""
        try:
            if sys.stdin is None:
                return
            while True:
                line = sys.stdin.readline()
                if line == "" or line.strip().lower() == "quit":
                    break
        except Exception:
            pass
        self.request_shutdown()
        # Normally the listener stops and the main thread ends the process. If
        # it does not (some systems), finish the job ourselves after a moment.
        time.sleep(1.0)
        self.finalize()
        os._exit(0)

    # --------------------------------------------------------------- main
    def run(self):
        print("=" * 52)
        print("       Smooth Numpad Mouse Controller")
        print("=" * 52)
        print("(NumLock must be ON)")
        print("Numpad - : Toggle mouse control ON/OFF")
        print("Numpad 8/2/4/6 : Move cursor")
        print("Numpad 7 : Hold left mouse button")
        print("Numpad 9 : Hold right mouse button")
        print("Numpad 5 : Hold middle mouse button")
        print("Hold Numpad 0 : Slow movement")
        print("Numpad 3 : Scroll up")
        print("Numpad , : Scroll down")
        print("Managed by UltimateHub" if self.managed else "Ctrl+C : Exit")
        print("=" * 52, flush=True)

        Thread(target=self.movement_worker, daemon=True).start()

        if IS_WINDOWS and hasattr(self.Listener, "suppress_event"):
            self.listener = self.Listener(win32_event_filter=self.win32_event_filter)
        else:
            if IS_WINDOWS:
                print("WARNING: pynput is older than 1.7, numpad keys cannot be "
                      "blocked. Run: pip install -U pynput", flush=True)
            self.listener = self.Listener(on_press=self.on_press, on_release=self.on_release)

        self.listener.start()
        if self.managed:
            Thread(target=self.watch_parent, daemon=True).start()

        try:
            self.listener.join()
        except KeyboardInterrupt:
            print("\nStopping controller...", flush=True)
        finally:
            try:
                self.listener.stop()
            except Exception:
                pass
            self.finalize()


def run_numouse(managed=False):
    """Entry point of the NuMouse background process."""
    if IS_WINDOWS:
        try:                          # exact cursor moves on scaled displays,
            import ctypes             # and a real 1 ms timer resolution
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
            except Exception:
                ctypes.windll.user32.SetProcessDPIAware()
            ctypes.windll.winmm.timeBeginPeriod(1)
        except Exception:
            pass
    from pynput.keyboard import Listener
    from pynput.mouse import Button, Controller as MouseController
    NuMouseEngine(MouseController(), Button, Listener, managed).run()


# ===========================================================================
#  SECTION 4 - WINDOWS 7 "AERO" TOOLKIT
#  Everything is drawn from pixel buffers (PhotoImage), so it looks the same
#  on every machine and does not depend on the OS theme.
# ===========================================================================

# ---- palette (sampled from the Windows 7 Aero look) -----------------------
GLASS_TOP = "#DCE9F8"
GLASS_MID = "#C6DAF1"
GLASS = "#B5CDEA"                 # window frame / address-bar area
FRAME_BORDER = "#4A5E7D"
FRAME_LIGHT = "#E9F2FC"
CLIENT_BORDER = "#6B7D98"
TRANS_KEY = "#FF00FF"             # transparent corners (Windows only)
CORNER = TRANS_KEY if IS_WINDOWS else FRAME_BORDER

WHITE = "#FFFFFF"
TEXT = "#000000"
TEXT_DIM = "#6D6D6D"
HEADING = "#1E3A78"
LINK = "#0066CC"
OK_GREEN = "#2E8B2E"
PANE_BG = "#FFFFFF"
NAV_BG = "#FFFFFF"
BAR_TOP = "#F7F9FC"
BAR_BOT = "#E4EAF3"
BAR_BORDER = "#C0CCDC"
SEL_TOP, SEL_BOT, SEL_BORDER = "#E9F3FE", "#D1E5FA", "#7DA2CE"
HOT_TOP, HOT_BOT, HOT_BORDER = "#F6FAFE", "#E5EFFB", "#B8D6FB"
DIALOG_BAR = "#F0F0F0"

UI_FONT = "Segoe UI"


def F(size=9, bold=False):
    return (UI_FONT, size, "bold") if bold else (UI_FONT, size)


_font_cache = {}


def text_width(text, font_spec):
    font = _font_cache.get(font_spec)
    if font is None:
        font = _font_cache[font_spec] = tkfont.Font(font=font_spec)
    return font.measure(text)


# ---- colour helpers --------------------------------------------------------

def _rgb(color):
    return int(color[1:3], 16), int(color[3:5], 16), int(color[5:7], 16)


def _hex(r, g, b):
    return "#%02x%02x%02x" % (max(0, min(255, int(round(r)))),
                              max(0, min(255, int(round(g)))),
                              max(0, min(255, int(round(b)))))


def blend(c1, c2, a):
    """a=0 -> c1, a=1 -> c2."""
    if a <= 0:
        return c1
    if a >= 1:
        return c2
    r1, g1, b1 = _rgb(c1)
    r2, g2, b2 = _rgb(c2)
    return _hex(r1 + (r2 - r1) * a, g1 + (g2 - g1) * a, b1 + (b2 - b1) * a)


def grad_color(stops, f):
    """stops = [(pos, color), ...]; equal positions make a hard step."""
    if f <= stops[0][0]:
        return stops[0][1]
    for index in range(1, len(stops)):
        p0, c0 = stops[index - 1]
        p1, c1 = stops[index]
        if f < p1 or (index == len(stops) - 1 and f <= p1):
            if p1 == p0:
                return c1
            return blend(c0, c1, (f - p0) / (p1 - p0))
    return stops[-1][1]


class Pix:
    """A tiny pixel buffer that can be turned into a Tk PhotoImage."""

    def __init__(self, w, h, bg=WHITE):
        self.w, self.h = w, h
        self.rows = [[bg] * w for _ in range(h)]

    def put(self, x, y, color):
        if 0 <= x < self.w and 0 <= y < self.h:
            self.rows[y][x] = color

    def mix(self, x, y, color, alpha):
        if 0 <= x < self.w and 0 <= y < self.h and alpha > 0:
            self.rows[y][x] = blend(self.rows[y][x], color, alpha)

    def image(self, master=None):
        image = tk.PhotoImage(master=master, width=self.w, height=self.h)
        image.put(" ".join("{" + " ".join(row) + "}" for row in self.rows))
        return image


def rr_cov(px, py, w, h, r):
    """Anti-aliased coverage (0..1) of a rounded rectangle at pixel (px, py)."""
    cx, cy = px + 0.5, py + 0.5
    if cx < 0 or cy < 0 or cx > w or cy > h:
        return 0.0
    dx = max(r - cx, 0.0, cx - (w - r))
    dy = max(r - cy, 0.0, cy - (h - r))
    if dx == 0.0 and dy == 0.0:
        return 1.0
    return max(0.0, min(1.0, r - math.hypot(dx, dy) + 0.5))


_image_cache = {}


def cached_image(key, builder, master=None):
    image = _image_cache.get(key)
    if image is None:
        image = _image_cache[key] = builder().image(master)
    return image


# ---- Aero push button ------------------------------------------------------

BUTTON_STYLES = {
    # state: (top1, top2, bottom1, bottom2, border, inner highlight)
    "normal": ("#F2F2F2", "#EBEBEB", "#DDDDDD", "#CFCFCF", "#707070", "#FCFCFC"),
    "hot": ("#EAF6FD", "#D9F0FC", "#BEE6FD", "#A7D9F5", "#3C7FB1", "#EEF9FE"),
    "down": ("#E5F4FC", "#C4E5F6", "#98D1EF", "#68B3DB", "#2C628B", "#8CC4E4"),
    "disabled": ("#F4F4F4", "#F4F4F4", "#F4F4F4", "#F4F4F4", "#ADB2B5", "#FAFAFA"),
    "default": ("#F2F2F2", "#EBEBEB", "#DDDDDD", "#CFCFCF", "#3C7FB1", "#A9DBF4"),
}


def build_button(w, h, state, bg):
    top1, top2, bot1, bot2, border, inner = BUTTON_STYLES[state]
    pix = Pix(w, h, bg)
    stops = [(0.0, top1), (0.5, top2), (0.5, bot1), (1.0, bot2)]
    for y in range(h):
        fill = grad_color(stops, (y + 0.5) / h)
        for x in range(w):
            outer = rr_cov(x, y, w, h, 3)
            if outer <= 0:
                continue
            inside = rr_cov(x - 1, y - 1, w - 2, h - 2, 2)
            colour = blend(border, fill, inside)
            hi = inside - rr_cov(x - 2, y - 2, w - 4, h - 4, 1)
            if hi > 0:
                colour = blend(colour, inner, hi * 0.9)
            pix.rows[y][x] = blend(bg, colour, outer)
    return pix


class AeroButton(tk.Canvas):
    """Windows 7 push button."""

    def __init__(self, parent, text, command=None, width=None, height=23,
                 default=False, font=None, bg=None):
        self.text = text
        self.command = command
        self.default = default
        self.font_spec = font or F(9)
        self._width = width or max(75, text_width(text, self.font_spec) + 28)
        self._height = height
        self._state = "normal"
        self._enabled = True
        self._inside = False
        bg = norm_color(parent, bg) if bg else _widget_bg(parent)
        super().__init__(parent, width=self._width, height=self._height, bg=bg,
                         highlightthickness=0, bd=0, cursor="arrow")
        self.bind("<Enter>", self._enter)
        self.bind("<Leave>", self._leave)
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<ButtonRelease-1>", self._release)
        self._draw()

    def _style_key(self):
        if not self._enabled:
            return "disabled"
        if self._state in ("hot", "down"):
            return self._state
        return "default" if self.default else "normal"

    def _draw(self):
        if not self.winfo_exists():
            return
        key = self._style_key()
        bg = self.cget("bg")
        image = cached_image(("btn", self._width, self._height, key, bg),
                             lambda: build_button(self._width, self._height, key, bg),
                             self)
        self.delete("all")
        self.create_image(0, 0, image=image, anchor="nw")
        self.create_text(self._width // 2, self._height // 2 - 1, text=self.text,
                         font=self.font_spec, anchor="center",
                         fill=TEXT if self._enabled else "#838383")

    def _enter(self, _e):
        self._inside = True
        if self._enabled and self._state != "down":
            self._state = "hot"
            self._draw()

    def _leave(self, _e):
        self._inside = False
        if self._enabled:
            self._state = "normal"
            self._draw()

    def _press(self, _e):
        if self._enabled:
            self._state = "down"
            self._draw()

    def _release(self, _e):
        if not self._enabled:
            return
        was_down = self._state == "down"
        self._state = "hot" if self._inside else "normal"
        self._draw()
        if was_down and self._inside:
            self.invoke()

    def invoke(self):
        if self._enabled and self.command:
            self.command()

    def set_enabled(self, enabled):
        self._enabled = bool(enabled)
        self._state = "normal"
        self._draw()

    def set_text(self, text):
        self.text = text
        self._draw()

    def set_bg(self, color):
        self.configure(bg=norm_color(self, color))
        self._draw()


def norm_color(widget, color):
    """Any Tk colour (name, #rgb, #rrggbb) -> '#rrggbb'."""
    if isinstance(color, str) and len(color) == 7 and color.startswith("#"):
        return color.lower()
    try:
        r, g, b = widget.winfo_rgb(color)
        return "#%02x%02x%02x" % (r >> 8, g >> 8, b >> 8)
    except tk.TclError:
        return WHITE


def _widget_bg(widget):
    try:
        return norm_color(widget, widget.cget("bg"))
    except tk.TclError:
        return WHITE


# ---- round "Back / Forward" orb ----------------------------------------------

ORB_STYLES = {
    "normal": ("#CFE3F8", "#7FB0E8", "#3A75C8", "#6FB4F2", "#2E4F82"),
    "hot": ("#E4F3FF", "#99CCF9", "#4C8FE0", "#8CD0FA", "#27508C"),
    "down": ("#9CC1EC", "#4F86CF", "#27589F", "#4C94DE", "#1F3F70"),
    "disabled": ("#F0F3F8", "#D9E0EA", "#C6D0DE", "#D9E0EA", "#9AA8BC"),
}


def build_orb(size, state, bg):
    top, mid, bottom, glow, ring = ORB_STYLES[state]
    pix = Pix(size, size, bg)
    r = size / 2.0
    cx = cy = r
    stops = [(0.0, top), (0.5, mid), (1.0, bottom)]
    for y in range(size):
        for x in range(size):
            d = math.hypot(x + 0.5 - cx, y + 0.5 - cy)
            cov = max(0.0, min(1.0, r - d + 0.5))
            if cov <= 0:
                continue
            body = grad_color(stops, (y + 0.5) / size)
            # warm glow at the bottom centre
            gd = math.hypot((x + 0.5 - cx) / (r * 0.8), (y + 0.5 - (cy + r * 0.55)) / (r * 0.5))
            if gd < 1:
                body = blend(body, glow, (1 - gd) * 0.65)
            # glossy highlight in the upper half
            hd = math.hypot((x + 0.5 - cx) / (r * 0.82), (y + 0.5 - (cy - r * 0.42)) / (r * 0.52))
            if hd < 1 and state != "disabled":
                body = blend(body, WHITE, 0.55 * (1 - hd * 0.55))
            # outer ring + soft inner ring
            edge = r - d
            colour = body
            if edge < 2.0:
                colour = blend(body, "#DCEBFA", 0.5 * max(0.0, 1 - abs(edge - 1.6)))
            if edge < 1.2:
                colour = blend(colour, ring, min(1.0, (1.2 - edge) / 1.2 + 0.25))
            pix.rows[y][x] = blend(bg, colour, cov)
    return pix


class OrbButton(tk.Canvas):
    """The round blue Back / Forward button of Windows 7 Explorer."""

    def __init__(self, parent, direction="back", command=None, size=30, enabled=True):
        self.direction = direction
        self.command = command
        self.size = size
        self._enabled = enabled
        self._state = "normal"
        self._inside = False
        super().__init__(parent, width=size, height=size, bg=_widget_bg(parent),
                         highlightthickness=0, bd=0, cursor="arrow")
        self.bind("<Enter>", self._enter)
        self.bind("<Leave>", self._leave)
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<ButtonRelease-1>", self._release)
        self._draw()

    def _draw(self):
        if not self.winfo_exists():
            return
        state = "disabled" if not self._enabled else self._state
        bg = self.cget("bg")
        image = cached_image(("orb", self.size, state, bg),
                             lambda: build_orb(self.size, state, bg), self)
        self.delete("all")
        self.create_image(0, 0, image=image, anchor="nw")
        c = self.size / 2.0
        k = self.size / 30.0
        sign = -1 if self.direction == "back" else 1
        pts = [(8, 0), (1, -7), (1, -3.2), (-8, -3.2), (-8, 3.2), (1, 3.2), (1, 7)]
        flat = []
        for px, py in pts:
            flat += [c + sign * px * k * 0.95, c + py * k * 0.95]
        fill = "#FFFFFF" if self._enabled else "#F7F9FC"
        outline = "#1D4A8A" if self._enabled else "#9AA8BC"
        self.create_polygon(*[v + (0.8 if i % 2 else 0.0) for i, v in enumerate(flat)],
                            fill="#1D3F73" if self._enabled else "", outline="")
        self.create_polygon(*flat, fill=fill, outline=outline, width=1)

    def _enter(self, _e):
        self._inside = True
        if self._enabled and self._state != "down":
            self._state = "hot"
            self._draw()

    def _leave(self, _e):
        self._inside = False
        self._state = "normal"
        self._draw()

    def _press(self, _e):
        if self._enabled:
            self._state = "down"
            self._draw()

    def _release(self, _e):
        if not self._enabled:
            return
        was_down = self._state == "down"
        self._state = "hot" if self._inside else "normal"
        self._draw()
        if was_down and self._inside:
            self.invoke()

    def invoke(self):
        if self._enabled and self.command:
            self.command()

    def set_enabled(self, enabled):
        self._enabled = bool(enabled)
        self._draw()


# ---- text box -----------------------------------------------------------------

class AeroEntry(tk.Frame):
    """Windows 7 text box (thin border that turns blue on hover / focus)."""

    def __init__(self, parent, textvariable=None, font=None, width=20,
                 placeholder=None, bg=WHITE):
        super().__init__(parent, bg="#ABADB3")
        self._focus = False
        self._hover = False
        self.var = textvariable or tk.StringVar()
        inner = tk.Frame(self, bg=bg)
        inner.pack(fill="both", expand=True, padx=1, pady=1)
        self.entry = tk.Entry(inner, textvariable=self.var, font=font or F(9), width=width,
                              relief="flat", bd=0, highlightthickness=0, bg=bg, fg=TEXT,
                              insertbackground=TEXT, disabledbackground=bg)
        self.entry.pack(fill="x", expand=True, padx=4, pady=3)
        self.placeholder = None
        if placeholder:
            self.placeholder = tk.Label(inner, text=placeholder, bg=bg, fg="#8B8B8B",
                                        font=font or F(9), cursor="xterm")
            self.placeholder.place(x=5, rely=0.5, anchor="w")
            self.placeholder.bind("<Button-1>", lambda e: self.entry.focus_set())
            self.var.trace_add("write", lambda *_: self._sync_placeholder())
            self._sync_placeholder()
        self.entry.bind("<FocusIn>", lambda e: self._set(focus=True))
        self.entry.bind("<FocusOut>", lambda e: self._set(focus=False))
        for widget in (self, inner, self.entry):
            widget.bind("<Enter>", lambda e: self._set(hover=True), add="+")
            widget.bind("<Leave>", lambda e: self._set(hover=False), add="+")

    def _sync_placeholder(self):
        if self.placeholder is None:
            return
        if self.var.get():
            self.placeholder.place_forget()
        else:
            self.placeholder.place(x=5, rely=0.5, anchor="w")

    def _set(self, focus=None, hover=None):
        if focus is not None:
            self._focus = focus
        if hover is not None:
            self._hover = hover
        self.configure(bg="#3D7BAD" if self._focus else ("#5794BF" if self._hover else "#ABADB3"))

    def set_state(self, state):
        self.entry.configure(state=state)


# ---- scrollbar + scroll frame -----------------------------------------------

def build_thumb(w, h, hot):
    pix = Pix(w, h, "#F0F0F0")
    stops = ([(0, "#EAF6FD"), (0.5, "#D9F0FC"), (0.5, "#BEE6FD"), (1, "#A7D9F5")] if hot
             else [(0, "#F6F6F6"), (0.5, "#E9E9E9"), (0.5, "#DADADA"), (1, "#CFCFCF")])
    border = "#3C7FB1" if hot else "#979797"
    for y in range(h):
        fill = grad_color(stops, (y + 0.5) / h)
        for x in range(w):
            outer = rr_cov(x, y, w, h, 3)
            if outer <= 0:
                continue
            inside = rr_cov(x - 1, y - 1, w - 2, h - 2, 2)
            pix.rows[y][x] = blend("#F0F0F0", blend(border, fill, inside), outer)
    return pix


class AeroScrollbar(tk.Canvas):
    def __init__(self, parent, command, width=17):
        super().__init__(parent, width=width, bg="#F0F0F0", highlightthickness=0, bd=0)
        self.command = command
        self.first, self.last = 0.0, 1.0
        self._hot = False
        self._drag = None
        self.bind("<Configure>", lambda e: self._draw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Enter>", lambda e: self._hover(True))
        self.bind("<Leave>", lambda e: self._hover(False))

    def set(self, first, last):
        self.first, self.last = float(first), float(last)
        self._draw()

    def _hover(self, hot):
        if self._drag is None:
            self._hot = hot
            self._draw()

    def _thumb(self):
        height = max(1, self.winfo_height())
        top = int(self.first * height)
        bottom = int(self.last * height)
        if bottom - top < 28:
            bottom = top + 28
            if bottom > height:
                bottom, top = height, height - 28
        return top, bottom, height

    def _draw(self):
        if not self.winfo_exists():
            return
        self.delete("all")
        width = int(self.cget("width"))
        self.create_line(0, 0, 0, 9999, fill="#E5E5E5")
        top, bottom, _ = self._thumb()
        hot = self._hot or self._drag is not None
        image = cached_image(("thumb", width - 4, bottom - top, hot),
                             lambda: build_thumb(width - 4, bottom - top, hot), self)
        self.create_image(2, top, image=image, anchor="nw")

    def _press(self, event):
        top, bottom, height = self._thumb()
        if top <= event.y <= bottom:
            self._drag = (event.y, self.first)
            self._draw()
        elif event.y < top:
            self.command("scroll", -1, "pages")
        else:
            self.command("scroll", 1, "pages")

    def _motion(self, event):
        if self._drag is None:
            return
        start_y, start_first = self._drag
        height = max(1, self.winfo_height())
        self.command("moveto", start_first + (event.y - start_y) / height)

    def _release(self, _e):
        self._drag = None
        self._draw()


class ScrollFrame(tk.Frame):
    """Vertically scrollable area: mouse wheel + an Aero scrollbar that only
    appears when the content does not fit."""

    def __init__(self, parent, bg=WHITE):
        super().__init__(parent, bg=bg)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0,
                                width=1, height=1, yscrollincrement=28)
        self.scrollbar = AeroScrollbar(self, self.canvas.yview)
        self.inner = tk.Frame(self.canvas, bg=bg)
        self._window = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.canvas.configure(yscrollcommand=self._on_scroll_set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner.bind("<Configure>",
                        lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>",
                         lambda e: self.canvas.itemconfigure(self._window, width=e.width))
        self.bind_all("<MouseWheel>", self._on_mousewheel)

    def destroy(self):
        try:
            self.unbind_all("<MouseWheel>")
        except tk.TclError:
            pass
        super().destroy()

    def _on_scroll_set(self, first, last):
        self.scrollbar.set(first, last)
        if float(first) <= 0.0 and float(last) >= 1.0:
            self.scrollbar.pack_forget()
        elif not self.scrollbar.winfo_manager():
            self.scrollbar.pack(side="right", fill="y", before=self.canvas)

    def _on_mousewheel(self, event):
        try:
            widget = self.winfo_containing(event.x_root, event.y_root)
        except (tk.TclError, KeyError):
            return
        while widget is not None:
            if widget is self:
                break
            widget = widget.master
        else:
            return
        if self.inner.winfo_reqheight() <= self.canvas.winfo_height():
            return
        self.canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")

    def scroll_to_end(self):
        self.update_idletasks()
        self.canvas.yview_moveto(1.0)


def set_bg_recursive(widget, color, skip=()):
    """Recolour a widget tree (used for the selected / hovered list rows)."""
    if widget in skip:
        return
    cls = widget.winfo_class()
    try:
        if hasattr(widget, "set_bg"):            # AeroButton, IconBox
            widget.set_bg(color)
        elif cls in ("Frame", "Label", "Canvas"):
            widget.configure(bg=color)
    except tk.TclError:
        pass
    for child in widget.winfo_children():
        set_bg_recursive(child, color, skip)


# ---- icons (drawn from pixel buffers, anti-aliased) -------------------------

def _shape(pix, w, h, r, border, stops, bg_cov=1.0):
    """Rounded box with border + vertical gradient (shared by the icons)."""
    for y in range(pix.h):
        fill = grad_color(stops, (y + 0.5) / pix.h)
        for x in range(pix.w):
            outer = rr_cov(x, y, w, h, r)
            if outer <= 0:
                continue
            inside = rr_cov(x - 1, y - 1, w - 2, h - 2, max(r - 1, 0.5))
            pix.rows[y][x] = blend(pix.rows[y][x], blend(border, fill, inside), outer * bg_cov)


def build_icon(kind, size, bg):
    s = size
    pix = Pix(s, s, bg)
    if kind == "hub":                                   # glossy blue "U" tile
        _shape(pix, s, s, s * 0.22, "#274C80",
               [(0, "#8BC0F5"), (0.5, "#3F86DC"), (0.5, "#2B6CC4"), (1, "#4C97E6")])
        for y in range(int(s * 0.5)):                   # gloss
            for x in range(s):
                if rr_cov(x - 1, y - 1, s - 2, s - 2, s * 0.2) > 0:
                    pix.mix(x, y, WHITE, 0.28 * (1 - y / (s * 0.5)) + 0.08)
    elif kind == "mouse":
        mw, mh = s * 0.56, s * 0.82
        ox, oy = (s - mw) / 2, s * 0.09
        for y in range(s):
            for x in range(s):
                cov = rr_cov(x - ox, y - oy, mw, mh, mw / 2)
                if cov <= 0:
                    continue
                inside = rr_cov(x - ox - 1, y - oy - 1, mw - 2, mh - 2, mw / 2 - 1)
                v = (y - oy) / mh
                fill = grad_color([(0, "#FFFFFF"), (1, "#C9D2DE")], v)
                if v < 0.42 and x < s / 2:               # pressed-looking left button
                    fill = blend(fill, "#9CC7F2", 0.55)
                pix.rows[y][x] = blend(bg, blend("#4F5D73", fill, inside), cov)
        split = int(oy + mh * 0.42)
        for x in range(int(ox + 2), int(ox + mw - 2)):
            pix.put(x, split, "#6F7D92")
        for y in range(int(oy + 2), split):
            pix.put(s // 2, y, "#6F7D92")
        for y in range(int(oy + mh * 0.12), int(oy + mh * 0.32)):   # wheel
            for x in (s // 2 - 1, s // 2):
                pix.put(x, y, "#34507C")
    elif kind == "image":
        px0, py0, pw, ph = s * 0.08, s * 0.16, s * 0.84, s * 0.68
        for y in range(s):
            for x in range(s):
                cov = rr_cov(x - px0, y - py0, pw, ph, 2)
                if cov <= 0:
                    continue
                inside = rr_cov(x - px0 - 3, y - py0 - 3, pw - 6, ph - 6, 1)
                u, v = (x - px0 - 3) / (pw - 6), (y - py0 - 3) / (ph - 6)
                sky = grad_color([(0, "#4C9BE8"), (1, "#CDE8FB")], max(0, min(1, v)))
                col = sky
                if math.hypot(u - 0.72, v - 0.3) < 0.13:                # sun
                    col = "#FFD94A"
                hill1 = 0.62 + 0.14 * math.sin(u * 3.4 + 0.6)
                hill2 = 0.74 + 0.10 * math.sin(u * 4.6 + 2.2)
                if v > hill1:
                    col = "#5FB04B"
                if v > hill2:
                    col = "#3F8E3C"
                inner = blend("#FFFFFF", col, inside)
                pix.rows[y][x] = blend(bg, blend("#7C879A", inner, min(1, inside + 0.0)), cov)
    elif kind in ("all", "tools", "apps", "running"):
        if kind == "all":
            for gx in (0, 1):
                for gy in (0, 1):
                    x0, y0 = int(s * (0.1 + gx * 0.46)), int(s * (0.1 + gy * 0.46))
                    side = int(s * 0.36)
                    for y in range(y0, y0 + side):
                        for x in range(x0, x0 + side):
                            cov = rr_cov(x - x0, y - y0, side, side, 1.5)
                            inner = grad_color([(0, "#8FC2F5"), (1, "#3D80D6")], (y - y0) / side)
                            pix.mix(x, y, blend("#2D5B9E", inner, rr_cov(x - x0 - 1, y - y0 - 1, side - 2, side - 2, 1)), cov)
        elif kind == "tools":
            return build_icon("hub", size, bg)
        elif kind == "apps":
            _shape(pix, s, s, 2, "#5F6E86", [(0, "#FFFFFF"), (1, "#DCE4EF")])
            for y in range(1, int(s * 0.3)):
                for x in range(1, s - 1):
                    pix.rows[y][x] = grad_color([(0, "#9CC7F4"), (1, "#4C8BDA")], y / (s * 0.3))
        else:                                                           # running
            r = s / 2.0
            for y in range(s):
                for x in range(s):
                    cov = max(0.0, min(1.0, r - math.hypot(x + .5 - r, y + .5 - r) + .5))
                    if cov > 0:
                        col = grad_color([(0, "#8EE19B"), (1, "#2E9E48")], y / s)
                        pix.rows[y][x] = blend(bg, blend("#237A38", col, min(1, r - math.hypot(x + .5 - r, y + .5 - r) - .4)), cov)
            for y in range(int(s * .28), int(s * .72)):                 # play triangle
                half = (y - s * .28) if y < s * .5 else (s * .72 - y)
                for x in range(int(s * .38), int(s * .38 + half * 1.15)):
                    pix.put(x, y, WHITE)
    elif kind in ("info", "question", "warning", "error"):
        base = {"info": ("#7DB6F3", "#2B6FCB", "#1D4F94"),
                "question": ("#7DB6F3", "#2B6FCB", "#1D4F94"),
                "error": ("#F19A8E", "#D14B3C", "#8E2519"),
                "warning": ("#FFE27A", "#F2B705", "#9A7000")}[kind]
        if kind == "warning":
            for y in range(s):
                for x in range(s):
                    hit = 0.0
                    for sx in (0.17, 0.5, 0.83):
                        for sy in (0.17, 0.5, 0.83):
                            u, v = (x + sx) / s, (y + sy) / s
                            if v >= 0.08 and abs(u - 0.5) <= (v - 0.08) * 0.56 + 0.0 and v <= 0.94:
                                hit += 1
                    cov = hit / 9.0
                    if cov > 0:
                        v = y / s
                        col = grad_color([(0, base[0]), (1, base[1])], v)
                        pix.rows[y][x] = blend(bg, blend(base[2], col, 0.85), cov)
        else:
            r = s / 2.0
            for y in range(s):
                for x in range(s):
                    d = math.hypot(x + .5 - r, y + .5 - r)
                    cov = max(0.0, min(1.0, r - d + .5))
                    if cov > 0:
                        col = grad_color([(0, base[0]), (0.5, base[1]), (1, base[1])], y / s)
                        if y < s * 0.45 and d < r * 0.9:
                            col = blend(col, WHITE, 0.25)
                        pix.rows[y][x] = blend(bg, blend(base[2], col, min(1, r - d - .2)), cov)
    return pix


def icon_image(kind, size, bg, master=None):
    return cached_image(("icon", kind, size, bg), lambda: build_icon(kind, size, bg), master)


class IconBox(tk.Canvas):
    """Item icon: a drawn icon, an .exe icon (PhotoImage) or a letter tile."""

    GLYPHS = {"info": ("i", WHITE), "question": ("?", WHITE),
              "error": ("X", WHITE), "warning": ("!", "#5A4200")}

    def __init__(self, parent, kind=None, size=40, image=None, letter="?", bg=None):
        self.kind, self.size, self.photo, self.letter = kind, size, image, letter
        super().__init__(parent, width=size, height=size,
                         bg=norm_color(parent, bg) if bg else _widget_bg(parent),
                         highlightthickness=0, bd=0)
        self._draw()

    def _draw(self):
        if not self.winfo_exists():
            return
        self.delete("all")
        bg = self.cget("bg")
        if self.photo is not None:
            self.create_image(self.size // 2, self.size // 2, image=self.photo)
        elif self.kind:
            self.create_image(0, 0, image=icon_image(self.kind, self.size, bg, self), anchor="nw")
            if self.kind == "hub":
                self.create_text(self.size // 2, self.size // 2 - 1, text="U", fill=WHITE,
                                 font=F(max(7, int(self.size * 0.42)), True))
            elif self.kind in self.GLYPHS:
                glyph, colour = self.GLYPHS[self.kind]
                self.create_text(self.size // 2, int(self.size * (0.62 if self.kind == "warning" else 0.5)),
                                 text=glyph, fill=colour, font=F(max(8, int(self.size * 0.5)), True))
        else:
            tile = cached_image(("tile", self.size, bg), lambda: self._tile(bg), self)
            self.create_image(0, 0, image=tile, anchor="nw")
            self.create_text(self.size // 2, self.size // 2 - 1, text=(self.letter or "?")[:1].upper(),
                             fill="#2C5AA0", font=F(max(8, int(self.size * 0.42)), True))

    def _tile(self, bg):
        pix = Pix(self.size, self.size, bg)
        _shape(pix, self.size, self.size, 5, "#8FA6C6", [(0, "#F4F8FD"), (1, "#CFDDF0")])
        return pix

    def set_bg(self, color):
        self.configure(bg=norm_color(self, color))
        self._draw()


# ---- window frame (glass title bar, borders, caption buttons) ---------------

def title_color(y, h):
    return grad_color([(0.0, GLASS_TOP), (0.45, GLASS_MID), (1.0, GLASS)], (y + 0.5) / h)


def build_title_parts(h, radius, square=False):
    """(left corner, 1px column, right corner) images of the glass title bar."""
    r = 0 if square else radius
    cw = max(r, 1) + 1
    left = Pix(cw, h, CORNER)
    right = Pix(cw, h, CORNER)
    col = Pix(1, h, GLASS)
    for y in range(h):
        base = title_color(y, h)
        if y == 0:
            col.rows[y][0] = FRAME_BORDER
        elif y == 1:
            col.rows[y][0] = blend(base, FRAME_LIGHT, 0.75)
        else:
            col.rows[y][0] = base
        for x in range(cw):
            if r:
                inside = rr_cov(x, y, cw * 4, h * 2, r) >= 0.5
                inner = rr_cov(x - 1, y - 1, cw * 4, h * 2, max(r - 1, 1)) >= 0.5
                inner2 = rr_cov(x - 2, y - 2, cw * 4, h * 2, max(r - 2, 1)) >= 0.5
            else:
                inside, inner, inner2 = True, x >= 1, x >= 2
            if not inside:
                continue
            colour = base if inner else FRAME_BORDER
            if inner and not inner2:
                colour = blend(base, FRAME_LIGHT, 0.75)
            if y == 0:
                colour = FRAME_BORDER
            left.rows[y][x] = colour
            right.rows[y][cw - 1 - x] = colour
    return left, col, right


def build_bottom_parts(h, radius, square=False):
    r = 0 if square else radius
    cw = max(r, 1) + 1
    left = Pix(cw, h, CORNER)
    right = Pix(cw, h, CORNER)
    col = Pix(1, h, GLASS)
    for y in range(h):
        col.rows[y][0] = FRAME_BORDER if y == h - 1 else GLASS
        for x in range(cw):
            if r:
                yy = h - 1 - y
                inside = rr_cov(x, yy, cw * 4, h * 2, r) >= 0.5
                inner = rr_cov(x - 1, yy - 1, cw * 4, h * 2, max(r - 1, 1)) >= 0.5
            else:
                inside, inner = True, x >= 1
            if not inside:
                continue
            colour = GLASS if (inner and y < h - 1) else FRAME_BORDER
            left.rows[y][x] = colour
            right.rows[y][cw - 1 - x] = colour
    return left, col, right


def _user32():
    import ctypes
    user32 = ctypes.windll.user32
    user32.GetParent.restype = ctypes.c_void_p
    user32.GetParent.argtypes = [ctypes.c_void_p]
    user32.ShowWindow.argtypes = [ctypes.c_void_p, ctypes.c_int]
    user32.GetWindowLongW.argtypes = [ctypes.c_void_p, ctypes.c_int]
    user32.SetWindowLongW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_long]
    user32.MonitorFromWindow.restype = ctypes.c_void_p
    user32.MonitorFromWindow.argtypes = [ctypes.c_void_p, ctypes.c_uint]
    user32.GetMonitorInfoW.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    return user32


def _hwnd(win):
    return _user32().GetParent(win.winfo_id())


def enable_taskbar_button(win):
    """A borderless (overrideredirect) window gets no taskbar button by default."""
    if not IS_WINDOWS:
        return
    try:
        user32 = _user32()
        hwnd = _hwnd(win)
        style = user32.GetWindowLongW(hwnd, -20)
        style = (style & ~0x00000080) | 0x00040000       # drop TOOLWINDOW, add APPWINDOW
        user32.SetWindowLongW(hwnd, -20, style)
        win.withdraw()
        win.after(60, win.deiconify)
    except Exception:
        pass


def work_area(win):
    """(x, y, w, h) of the usable desktop area (excludes the taskbar)."""
    if IS_WINDOWS:
        try:
            import ctypes
            from ctypes import wintypes

            class MONITORINFO(ctypes.Structure):
                _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT),
                            ("rcWork", wintypes.RECT), ("dwFlags", wintypes.DWORD)]
            user32 = _user32()
            monitor = user32.MonitorFromWindow(_hwnd(win), 2)
            info = MONITORINFO()
            info.cbSize = ctypes.sizeof(info)
            if user32.GetMonitorInfoW(monitor, ctypes.byref(info)):
                r = info.rcWork
                return r.left, r.top, r.right - r.left, r.bottom - r.top
        except Exception:
            pass
    return 0, 0, win.winfo_screenwidth(), win.winfo_screenheight()


def resize_cursor(edge):
    if IS_WINDOWS:
        table = {"e": "size_we", "w": "size_we", "n": "size_ns", "s": "size_ns",
                 "se": "size_nw_se", "nw": "size_nw_se", "ne": "size_ne_sw", "sw": "size_ne_sw"}
    else:
        table = {"e": "sb_h_double_arrow", "w": "sb_h_double_arrow",
                 "n": "sb_v_double_arrow", "s": "sb_v_double_arrow",
                 "se": "bottom_right_corner", "sw": "bottom_left_corner",
                 "nw": "top_left_corner", "ne": "top_right_corner"}
    return table.get(edge, "arrow")


CAPTION_STYLES = {
    # state: (top, bottom, border)
    "normal": ("#E3ECF8", "#A9C3E4", "#4F6485"),
    "hot": ("#E1F6FF", "#7ECBF2", "#2F6C9D"),
    "down": ("#9CC8E8", "#5E9CCB", "#244F78"),
    "close": ("#EAB5AB", "#C4574B", "#5E2B26"),
    "close_hot": ("#F5B3A8", "#E0402F", "#7A1F16"),
    "close_down": ("#D88A7E", "#A92E22", "#5A1912"),
}


class CaptionButton(tk.Canvas):
    SIZES = {"min": 28, "max": 27, "close": 47}
    HEIGHT = 19

    def __init__(self, parent, kind, command, bar_height):
        self.kind, self.command = kind, command
        self.bar_height = bar_height
        self.glyph = kind                      # "max" turns into "restore"
        self._state = "normal"
        self._inside = False
        w = self.SIZES[kind]
        super().__init__(parent, width=w, height=self.HEIGHT, highlightthickness=0, bd=0,
                         bg=GLASS_MID, cursor="arrow")
        self.bind("<Enter>", lambda e: self._set("hot", True))
        self.bind("<Leave>", lambda e: self._set("normal", False))
        self.bind("<ButtonPress-1>", lambda e: self._set("down"))
        self.bind("<ButtonRelease-1>", self._release)
        self._draw()

    def _set(self, state, inside=None):
        if inside is not None:
            self._inside = inside
        self._state = state
        self._draw()

    def _release(self, _e):
        was_down = self._state == "down"
        self._state = "hot" if self._inside else "normal"
        self._draw()
        if was_down and self._inside and self.command:
            self.command()

    def set_glyph(self, glyph):
        self.glyph = glyph
        self._draw()

    def _build(self, style):
        w, h = self.SIZES[self.kind], self.HEIGHT
        top, bottom, border = CAPTION_STYLES[style]
        pix = Pix(w, h, GLASS)
        for y in range(h):
            row_bg = title_color(y + 1, self.bar_height)
            for x in range(w):
                pix.rows[y][x] = row_bg
                inside = True                    # bottom corners rounded, top flush
                if y >= h - 4:
                    cx = min(x, w - 1 - x)
                    dy = y - (h - 5)
                    inside = (4 - cx) ** 2 + dy ** 2 <= 16.5 or cx >= 4
                if not inside:
                    continue
                edge = x == 0 or x == w - 1 or y == h - 1 or y == 0
                if y >= h - 4 and not edge:
                    cx = min(x, w - 1 - x)
                    dy = y - (h - 5)
                    edge = (4 - cx) ** 2 + dy ** 2 > 9.5 and cx < 4
                if edge:
                    pix.rows[y][x] = border
                else:
                    mix = (y - 1) / (h - 2)
                    colour = blend(top, bottom, mix) if mix > 0.45 else blend(top, blend(top, bottom, 0.45), mix / 0.45)
                    if mix < 0.5:
                        colour = blend(colour, WHITE, 0.25 * (1 - mix * 2))
                    pix.rows[y][x] = colour
        return pix

    def _draw(self):
        if not self.winfo_exists():
            return
        style = self._state if self.kind != "close" else (
            {"normal": "close", "hot": "close_hot", "down": "close_down"}[self._state])
        image = cached_image(("cap", self.kind, style, self.bar_height),
                             lambda: self._build(style), self)
        self.delete("all")
        self.create_image(0, 0, image=image, anchor="nw")
        w, h = self.SIZES[self.kind], self.HEIGHT
        cx, cy = w // 2, h // 2
        white = "#FFFFFF"
        shadow = "#2A3F5F" if self.kind != "close" else "#5A1912"
        for dx, dy, col in ((1, 1, shadow), (0, 0, white)):
            x, y = cx + dx, cy + dy
            if self.glyph == "min":
                self.create_rectangle(x - 5, y + 2, x + 4, y + 4, fill=col, outline=col)
            elif self.glyph == "max":
                self.create_rectangle(x - 5, y - 4, x + 5, y + 4, outline=col, width=1)
                self.create_line(x - 5, y - 3, x + 5, y - 3, fill=col, width=2)
            elif self.glyph == "restore":
                self.create_rectangle(x - 5, y - 2, x + 2, y + 4, outline=col, width=1)
                self.create_line(x - 5, y - 1, x + 2, y - 1, fill=col, width=2)
                self.create_line(x - 2, y - 4, x + 5, y - 4, x + 5, y + 2, fill=col, width=1)
            else:
                self.create_line(x - 5, y - 4, x + 5, y + 4, fill=col, width=2)
                self.create_line(x - 5, y + 4, x + 5, y - 4, fill=col, width=2)


class AeroWindow:
    """
    Gives a Tk / Toplevel window the Windows 7 Aero look: glass title bar with
    caption buttons, glass borders, drag / resize / maximize / minimize.
    Falls back to the normal system frame if USE_AERO_FRAME is False.

        .glass   frame for toolbars / the address bar (on the glass)
        .client  the white work area
    """
    FRAME_W = 8
    TITLE_H = 31
    RADIUS = 7

    def __init__(self, win, title, resizable=True, minimizable=True, maximizable=True,
                 on_close=None, taskbar=False, min_size=(320, 200), with_glass=True):
        self.win = win
        self.title_text = title
        self.resizable = resizable
        self.on_close = on_close
        self.min_w, self.min_h = min_size
        self.custom = USE_AERO_FRAME
        self.maximized = False
        self._restore_geometry = None
        self._rs = None
        self._move = None
        self.glass = None

        if not self.custom:
            win.title(title)
            win.configure(bg=GLASS)
            if with_glass:
                self.glass = tk.Frame(win, bg=GLASS)
                self.glass.pack(fill="x")
            self.client = tk.Frame(win, bg=WHITE)
            self.client.pack(fill="both", expand=True)
            win.protocol("WM_DELETE_WINDOW", self.close)
            return

        win.overrideredirect(True)
        if IS_WINDOWS:
            win.configure(bg=TRANS_KEY)
            try:
                win.attributes("-transparentcolor", TRANS_KEY)
            except tk.TclError:
                win.configure(bg=FRAME_BORDER)
        else:
            win.configure(bg=FRAME_BORDER)
        win.grid_columnconfigure(1, weight=1)
        win.grid_rowconfigure(2, weight=1)

        self.titlebar = tk.Canvas(win, height=self.TITLE_H, bg=CORNER, highlightthickness=0, bd=0)
        self.titlebar.grid(row=0, column=0, columnspan=3, sticky="ew")
        self.buttons = []
        self.btn_close = CaptionButton(self.titlebar, "close", self.close, self.TITLE_H)
        self.btn_close.place(relx=1.0, x=-8, y=1, anchor="ne")
        self.btn_max = self.btn_min = None
        if maximizable and resizable:
            self.btn_max = CaptionButton(self.titlebar, "max", self.toggle_maximize, self.TITLE_H)
            self.btn_max.place(relx=1.0, x=-8 - 47 + 1, y=1, anchor="ne")
        if minimizable:
            offset = 8 + 47 - 1 + (27 - 1 if self.btn_max else 0)
            self.btn_min = CaptionButton(self.titlebar, "min", self.minimize, self.TITLE_H)
            self.btn_min.place(relx=1.0, x=-offset, y=1, anchor="ne")
        self.titlebar.bind("<Configure>", lambda e: self._draw_title())
        self.titlebar.bind("<ButtonPress-1>", self._title_press)
        self.titlebar.bind("<B1-Motion>", self._title_drag)
        self.titlebar.bind("<ButtonRelease-1>", lambda e: self._end_drag())
        self.titlebar.bind("<Motion>", self._title_motion)
        self.titlebar.bind("<Double-Button-1>", lambda e: self.toggle_maximize())

        if with_glass:
            outer = tk.Frame(win, bg=FRAME_BORDER)
            outer.grid(row=1, column=0, columnspan=3, sticky="ew")
            self.glass = tk.Frame(outer, bg=GLASS)
            self.glass.pack(fill="x", padx=1)
        self.left = self._side("w", 0)
        self.right = self._side("e", 2)
        outer_client = tk.Frame(win, bg=CLIENT_BORDER)
        outer_client.grid(row=2, column=1, sticky="nsew")
        self.client = tk.Frame(outer_client, bg=WHITE)
        self.client.pack(fill="both", expand=True, padx=1, pady=1)
        self.bottom = tk.Canvas(win, height=self.FRAME_W, bg=CORNER, highlightthickness=0, bd=0)
        self.bottom.grid(row=3, column=0, columnspan=3, sticky="ew")
        self.bottom.bind("<Configure>", lambda e: self._draw_bottom())
        self.bottom.bind("<Motion>", self._bottom_motion)
        self.bottom.bind("<ButtonPress-1>", self._bottom_press)
        self.bottom.bind("<B1-Motion>", self._do_resize)
        self.bottom.bind("<ButtonRelease-1>", lambda e: self._end_drag())
        win.protocol("WM_DELETE_WINDOW", self.close)
        if taskbar:
            win.after(50, lambda: enable_taskbar_button(win))

    # ------------------------------------------------------------ drawing
    def _side(self, edge, column):
        frame = tk.Frame(self.win, bg=FRAME_BORDER, width=self.FRAME_W)
        frame.grid(row=2, column=column, sticky="ns")
        frame.grid_propagate(False)
        inner = tk.Frame(frame, bg=GLASS)
        if edge == "w":
            inner.place(x=1, y=0, relwidth=1.0, width=-1, relheight=1.0)
        else:
            inner.place(x=0, y=0, relwidth=1.0, width=-1, relheight=1.0)
        if self.resizable:
            for widget in (frame, inner):
                widget.configure(cursor=resize_cursor(edge))
                widget.bind("<ButtonPress-1>", lambda e, ed=edge: self._start_resize(ed, e))
                widget.bind("<B1-Motion>", self._do_resize)
                widget.bind("<ButtonRelease-1>", lambda e: self._end_drag())
        return frame

    def _draw_title(self):
        w, h = self.titlebar.winfo_width(), self.TITLE_H
        if w < 40:
            return
        sq = self.maximized
        left, col, right = (cached_image(("tp", i, h, sq), lambda i=i: build_title_parts(h, self.RADIUS, sq)[i], self.titlebar)
                            for i in range(3))
        cw = left.width()
        mid = col.zoom(max(1, w - 2 * cw), 1)
        self._title_imgs = (left, mid, right)
        c = self.titlebar
        c.delete("bg")
        c.create_image(0, 0, image=left, anchor="nw", tags="bg")
        c.create_image(cw, 0, image=mid, anchor="nw", tags="bg")
        c.create_image(w - cw, 0, image=right, anchor="nw", tags="bg")
        c.tag_lower("bg")
        c.delete("content")
        c.create_image(9, 7, image=icon_image("hub", 16, title_color(7, h), c), anchor="nw", tags="content")
        c.create_text(17, 14, text="U", fill=WHITE, font=F(7, True), tags="content")
        x = 32
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1), (-1, 1), (1, -1)):
            c.create_text(x + dx, 15 + dy, text=self.title_text, anchor="w", fill="#F4F9FF",
                          font=F(9), tags="content")
        c.create_text(x, 15, text=self.title_text, anchor="w", fill=TEXT, font=F(9), tags="content")

    def _draw_bottom(self):
        w, h = self.bottom.winfo_width(), self.FRAME_W
        if w < 40:
            return
        sq = self.maximized
        left, col, right = (cached_image(("bp", i, h, sq), lambda i=i: build_bottom_parts(h, 6, sq)[i], self.bottom)
                            for i in range(3))
        cw = left.width()
        mid = col.zoom(max(1, w - 2 * cw), 1)
        self._bottom_imgs = (left, mid, right)
        c = self.bottom
        c.delete("all")
        c.create_image(0, 0, image=left, anchor="nw")
        c.create_image(cw, 0, image=mid, anchor="nw")
        c.create_image(w - cw, 0, image=right, anchor="nw")

    def set_title(self, text):
        self.title_text = text
        if self.custom:
            self._draw_title()
        else:
            self.win.title(text)

    # ---------------------------------------------------- move / resize
    def _end_drag(self):
        self._move = None
        self._rs = None

    def _title_edge(self, event):
        if not self.resizable or self.maximized or event.y > 4:
            return None
        width = self.titlebar.winfo_width()
        if event.x < 10:
            return "nw"
        if event.x > width - 10:
            return "ne"
        return "n"

    def _title_motion(self, event):
        edge = self._title_edge(event)
        self.titlebar.configure(cursor=resize_cursor(edge) if edge else "arrow")

    def _title_press(self, event):
        edge = self._title_edge(event)
        if edge:
            self._start_resize(edge, event)
        elif not self.maximized:
            self._move = (event.x_root - self.win.winfo_x(), event.y_root - self.win.winfo_y())

    def _title_drag(self, event):
        if self._rs:
            self._do_resize(event)
        elif self._move:
            self.win.geometry("+%d+%d" % (event.x_root - self._move[0], event.y_root - self._move[1]))

    def _bottom_edge(self, event):
        width = self.bottom.winfo_width()
        if event.x < 12:
            return "sw"
        if event.x > width - 12:
            return "se"
        return "s"

    def _bottom_motion(self, event):
        self.bottom.configure(cursor=resize_cursor(self._bottom_edge(event)) if self.resizable else "arrow")

    def _bottom_press(self, event):
        if self.resizable:
            self._start_resize(self._bottom_edge(event), event)

    def _start_resize(self, edge, event):
        if self.maximized:
            return
        win = self.win
        self._rs = (edge, event.x_root, event.y_root, win.winfo_x(), win.winfo_y(),
                    win.winfo_width(), win.winfo_height())

    def _do_resize(self, event):
        if not self._rs:
            return
        edge, px, py, x, y, w, h = self._rs
        dx, dy = event.x_root - px, event.y_root - py
        nx, ny, nw, nh = x, y, w, h
        if "e" in edge:
            nw = max(self.min_w, w + dx)
        if "s" in edge:
            nh = max(self.min_h, h + dy)
        if "w" in edge:
            nw = max(self.min_w, w - dx)
            nx = x + (w - nw)
        if "n" in edge:
            nh = max(self.min_h, h - dy)
            ny = y + (h - nh)
        self.win.geometry("%dx%d+%d+%d" % (nw, nh, nx, ny))

    # ------------------------------------------------------ window actions
    def minimize(self):
        if IS_WINDOWS and self.custom:
            try:
                _user32().ShowWindow(_hwnd(self.win), 6)       # SW_MINIMIZE
                return
            except Exception:
                pass
        try:
            self.win.iconify()
        except tk.TclError:
            pass

    def toggle_maximize(self):
        if not (self.custom and self.resizable):
            return
        if not self.maximized:
            self._restore_geometry = self.win.geometry()
            x, y, w, h = work_area(self.win)
            self.win.geometry("%dx%d+%d+%d" % (w, h, x, y))
            self.maximized = True
        else:
            if self._restore_geometry:
                self.win.geometry(self._restore_geometry)
            self.maximized = False
        if self.btn_max:
            self.btn_max.set_glyph("restore" if self.maximized else "max")
        self._draw_title()
        self._draw_bottom()

    def close(self):
        if self.on_close:
            self.on_close()
        else:
            self.win.destroy()

    def center_on(self, owner=None, width=None, height=None):
        self.win.update_idletasks()
        w = width or self.win.winfo_reqwidth()
        h = height or self.win.winfo_reqheight()
        if owner is not None and owner.winfo_viewable():
            x = owner.winfo_x() + (owner.winfo_width() - w) // 2
            y = owner.winfo_y() + (owner.winfo_height() - h) // 3
        else:
            x = (self.win.winfo_screenwidth() - w) // 2
            y = (self.win.winfo_screenheight() - h) // 3
        self.win.geometry("%dx%d+%d+%d" % (w, h, max(0, x), max(0, y)))


# ---- Windows 7 style message / task dialog ------------------------------------

def aero_dialog(owner, heading, message="", kind="info", buttons=("OK",),
                default=0, cancel=None, width=460):
    """
    Modal Windows-7-style dialog. Returns the index of the pressed button.
    `owner` is the main Tk window (or any widget of it).
    """
    top = owner.winfo_toplevel()
    dlg = tk.Toplevel(top)
    dlg.withdraw()
    chrome = AeroWindow(dlg, APP_NAME, resizable=False, minimizable=False, maximizable=False,
                        with_glass=False)
    result = {"value": cancel if cancel is not None else (len(buttons) - 1 if len(buttons) > 1 else 0)}
    done = tk.BooleanVar(value=False)

    def finish(index):
        result["value"] = index
        done.set(True)

    chrome.on_close = lambda: finish(cancel if cancel is not None else result["value"])

    body = tk.Frame(chrome.client, bg=WHITE)
    body.pack(fill="both", expand=True)
    row = tk.Frame(body, bg=WHITE)
    row.pack(fill="both", expand=True, padx=22, pady=(20, 18))
    IconBox(row, kind=kind, size=32, bg=WHITE).pack(side="left", anchor="n", padx=(0, 14))
    text = tk.Frame(row, bg=WHITE)
    text.pack(side="left", fill="both", expand=True)
    tk.Label(text, text=heading, bg=WHITE, fg="#003399", font=F(12), justify="left",
             anchor="w", wraplength=width - 120).pack(anchor="w", fill="x")
    if message:
        tk.Label(text, text=message, bg=WHITE, fg=TEXT, font=F(9), justify="left",
                 anchor="w", wraplength=width - 120).pack(anchor="w", fill="x", pady=(10, 0))

    tk.Frame(chrome.client, bg="#DFDFDF", height=1).pack(fill="x")
    bar = tk.Frame(chrome.client, bg=DIALOG_BAR)
    bar.pack(fill="x")
    made = []
    for index in range(len(buttons) - 1, -1, -1):
        button = AeroButton(bar, buttons[index], lambda i=index: finish(i), width=88,
                            default=(index == default), bg=DIALOG_BAR)
        button.pack(side="right", padx=(0, 10 if index == len(buttons) - 1 else 8), pady=11)
        made.append(button)

    def on_return(_e=None):
        finish(default)

    def on_escape(_e=None):
        finish(cancel if cancel is not None else result["value"])

    dlg.bind("<Return>", on_return)
    dlg.bind("<Escape>", on_escape)
    dlg.configure(width=width)
    chrome.center_on(top if top.winfo_viewable() else None, width=width)
    dlg.deiconify()
    dlg.update_idletasks()
    try:
        dlg.transient(top)
        dlg.wait_visibility()
        dlg.grab_set()
    except tk.TclError:
        pass
    dlg.focus_force()
    dlg.wait_variable(done)
    try:
        dlg.grab_release()
    except tk.TclError:
        pass
    dlg.destroy()
    return result["value"]


# ---- background picture ------------------------------------------------------
# The picture is embedded in this file (WALLPAPER_B64, bottom of the file). It is
# scaled like a CSS "background-size: cover": the whole area is filled, the aspect
# ratio is kept and the overflow is cropped at the edges (centred). A white veil
# is blended over it so it never competes with the content. When the window is
# resized it is redrawn once the size settles (debounced).

WALLPAPER_VEIL = 0.50          # 0 = raw picture, 1 = plain white
CARD_BORDER = "#A9BBD3"

_wall = {}


def load_wallpaper():
    """Decoded background picture (PIL), or None if unavailable."""
    if Image is None or _wall.get("failed"):
        return None
    image = _wall.get("image")
    if image is None:
        try:
            image = Image.open(io.BytesIO(base64.b64decode(WALLPAPER_B64))).convert("RGB")
            _wall["image"] = image
        except Exception:
            _wall["failed"] = True
            return None
    return image


def render_wallpaper(width, height, veil=WALLPAPER_VEIL):
    """The picture, covering width x height, under the white veil (PIL image)."""
    base = load_wallpaper()
    if base is None or width < 2 or height < 2:
        return None
    bw, bh = base.size
    scale = max(width / bw, height / bh)
    nw, nh = max(width, int(math.ceil(bw * scale))), max(height, int(math.ceil(bh * scale)))
    resized = base.resize((nw, nh), Image.BILINEAR if scale > 1 else Image.LANCZOS)
    left, top = (nw - width) // 2, (nh - height) // 2
    cropped = resized.crop((left, top, left + width, top + height))
    return Image.blend(cropped, Image.new("RGB", cropped.size, (255, 255, 255)), veil)


def wallpaper_average():
    """Average colour of the veiled picture (shown while a resize catches up)."""
    base = load_wallpaper()
    if base is None:
        return "#DCE9F5"
    r, g, b = base.resize((1, 1), Image.BOX).getpixel((0, 0))
    return _hex(r + (255 - r) * WALLPAPER_VEIL, g + (255 - g) * WALLPAPER_VEIL,
                b + (255 - b) * WALLPAPER_VEIL)


def pil_to_photo(image, master):
    """PIL image -> Tk PhotoImage through PNG (no ImageTk dependency)."""
    buffer = io.BytesIO()
    image.save(buffer, format="PNG", compress_level=1)
    return tk.PhotoImage(master=master, data=base64.b64encode(buffer.getvalue()))


class WallpaperCanvas(tk.Canvas):
    """A canvas whose background is the veiled picture. Put cards / panels on it."""

    def __init__(self, parent):
        super().__init__(parent, highlightthickness=0, bd=0, bg=wallpaper_average())
        self._photo = None
        self._size = None
        self._job = None
        self.bind("<Configure>", self._on_configure)

    def _on_configure(self, _event=None):
        if self._job is not None:
            self.after_cancel(self._job)
        self._job = self.after(35, self.redraw)

    def redraw(self):
        self._job = None
        if not self.winfo_exists():
            return
        size = (self.winfo_width(), self.winfo_height())
        if size == self._size or size[0] < 2 or size[1] < 2:
            return
        image = render_wallpaper(*size)
        if image is None:
            return                              # no Pillow: plain colour stays
        try:
            self._photo = pil_to_photo(image, self)
        except tk.TclError:
            return
        self._size = size
        self.delete("wall")
        self.create_image(0, 0, image=self._photo, anchor="nw", tags="wall")
        self.tag_lower("wall")

    def destroy(self):
        if self._job is not None:
            try:
                self.after_cancel(self._job)
            except tk.TclError:
                pass
            self._job = None
        super().destroy()


def card(parent, bg=WHITE):
    """A white panel with a thin border, to sit on the wallpaper."""
    return tk.Frame(parent, bg=bg, highlightthickness=1, highlightbackground=CARD_BORDER)


# ===========================================================================
#  SECTION 5 - PAGES (OpenImage, NuMouse)
# ===========================================================================

def section(parent, title, bg=WHITE):
    """Windows 7 section heading: title text followed by a thin rule."""
    box = tk.Frame(parent, bg=bg)
    head = tk.Frame(box, bg=bg)
    head.pack(fill="x")
    tk.Label(head, text=title, bg=bg, fg=HEADING, font=F(10)).pack(side="left")
    tk.Frame(head, bg="#D5DFE5", height=1).pack(side="left", fill="x", expand=True,
                                                padx=(8, 0), pady=(3, 0))
    body = tk.Frame(box, bg=bg)
    body.pack(fill="both", expand=True, pady=(8, 0))
    return box, body


def page_heading(parent, title, subtitle=""):
    tk.Label(parent, text=title, bg=WHITE, fg=HEADING, font=F(15), anchor="w").pack(anchor="w")
    if subtitle:
        tk.Label(parent, text=subtitle, bg=WHITE, fg=TEXT_DIM, font=F(9),
                 anchor="w").pack(anchor="w", pady=(2, 0))


class OpenImagePage:
    """Image privacy tool: strips metadata or writes random phone EXIF."""

    def __init__(self, app, parent):
        self.app = app
        self.root = parent
        self.source_path = None
        self.source_format = None
        self.output_dir = tk.StringVar(value=str(desktop_path()))
        self.output_name = tk.StringVar(value="")
        self.output_format = tk.StringVar(value="Original format")
        self.quality_mode = tk.StringVar(value=QUALITY_HIGH)
        self.random_exif = tk.BooleanVar(value=False)
        self.downscale = tk.BooleanVar(value=False)
        self.location = tk.BooleanVar(value=False)
        self.source_size = None
        self.status = tk.StringVar(value="Choose an image to get started.")
        self.file_info = tk.StringVar(value="No image selected")
        self.build_ui()

    EXIF_TEXT = ("The copy gets realistic EXIF data (model, lens, ISO, exposure, date) of a "
                 "random popular phone out of 30, instead of staying clean.")
    ANDROID_TEXT = "Only Android phones are picked in this mode."
    RESIZE_TEXT = "Shrinks the picture a little (3024 x 4032 becomes 3000 x 4000), cropping nothing."
    LOCATION_TEXT = "Adds a random GPS spot on land (never in the sea) with a matching time zone."
    LOCATION_ON_TEXT = "A random GPS spot on land will be written, with a matching time zone."

    # ------------------------------------------------------------------ UI
    def build_ui(self):
        outer = tk.Frame(self.root, bg=WHITE)
        outer.pack(fill="both", expand=True)

        footer = tk.Frame(outer, bg=DIALOG_BAR)
        footer.pack(side="bottom", fill="x")
        tk.Frame(footer, bg="#DFDFDF", height=1).pack(fill="x")
        foot_row = tk.Frame(footer, bg=DIALOG_BAR)
        foot_row.pack(fill="x", padx=14, pady=10)
        self.save_button = AeroButton(foot_row, "Remove metadata & save",
                                      self.process_image, width=190, default=True, bg=DIALOG_BAR)
        self.save_button.pack(side="right")
        tk.Label(foot_row, textvariable=self.status, bg=DIALOG_BAR, fg=OK_GREEN, font=F(9),
                 anchor="w", justify="left", wraplength=470).pack(side="left", fill="x", expand=True)

        self.scroll = ScrollFrame(outer, WHITE)
        self.scroll.pack(fill="both", expand=True)
        content = tk.Frame(self.scroll.inner, bg=WHITE)
        content.pack(fill="both", expand=True, padx=24, pady=(14, 10))
        page_heading(content, "Clean or disguise your image",
                     "The original image is never modified. A new copy is exported.")

        box, body = section(content, "1.  Select image")
        box.pack(fill="x", pady=(14, 0))
        row = tk.Frame(body, bg=WHITE)
        row.pack(fill="x")
        tk.Label(row, textvariable=self.file_info, bg=WHITE, fg=TEXT, font=F(9), anchor="w",
                 justify="left", wraplength=560).pack(side="left", fill="x", expand=True)
        AeroButton(row, "Browse...", self.choose_image, default=True).pack(side="right")

        columns = tk.Frame(content, bg=WHITE)
        columns.pack(fill="both", expand=True, pady=(14, 0))
        columns.grid_columnconfigure(0, weight=1, uniform="cols")
        columns.grid_columnconfigure(1, weight=1, uniform="cols")

        left_box, left = section(columns, "2.  Output settings")
        left_box.grid(row=0, column=0, sticky="nsew", padx=(0, 14))
        tk.Label(left, text="Save folder", bg=WHITE, fg=TEXT_DIM, font=F(9)).pack(anchor="w")
        folder_row = tk.Frame(left, bg=WHITE)
        folder_row.pack(fill="x", pady=(3, 8))
        AeroButton(folder_row, "Change...", self.choose_folder, width=80).pack(side="right", padx=(6, 0))
        AeroEntry(folder_row, textvariable=self.output_dir).pack(side="left", fill="x", expand=True)
        tk.Label(left, text="Output filename (random by default)", bg=WHITE, fg=TEXT_DIM,
                 font=F(9)).pack(anchor="w")
        AeroEntry(left, textvariable=self.output_name).pack(fill="x", pady=(3, 8))
        tk.Checkbutton(left, text="Write random EXIF (fake phone)", variable=self.random_exif,
                       command=self.update_exif_hint, bg=WHITE, activebackground=WHITE,
                       fg=TEXT, selectcolor=WHITE, font=F(9, True), anchor="w",
                       highlightthickness=0, bd=0, cursor="arrow").pack(anchor="w")
        self.exif_hint = tk.Label(
            left, bg=WHITE, fg=TEXT_DIM, font=F(8), justify="left", anchor="w", wraplength=340,
            text=self.EXIF_TEXT)
        self.exif_hint.pack(anchor="w", fill="x", pady=(2, 0))
        # Greyed out until "Write random EXIF" is ticked.
        self.downscale_check = tk.Checkbutton(
            left, text="Slightly reduce the resolution", variable=self.downscale,
            command=self.update_resize_hint, state="disabled", bg=WHITE, activebackground=WHITE,
            fg=TEXT, disabledforeground="#9A9A9A", selectcolor=WHITE, font=F(9), anchor="w",
            highlightthickness=0, bd=0, cursor="arrow")
        self.downscale_check.pack(anchor="w", padx=(20, 0), pady=(8, 0))
        self.resize_hint = tk.Label(left, bg=WHITE, fg="#9A9A9A", font=F(8), justify="left",
                                    anchor="w", wraplength=320, text=self.RESIZE_TEXT)
        self.resize_hint.pack(anchor="w", fill="x", padx=(20, 0), pady=(2, 0))
        # shown only while the option is ticked
        self.resize_note = tk.Label(left, bg=WHITE, fg=TEXT_DIM, font=F(8), justify="left",
                                    anchor="w", wraplength=320, text=self.ANDROID_TEXT)
        self.location_check = tk.Checkbutton(
            left, text="Add random location (on land)", variable=self.location,
            command=self.update_location_hint, state="disabled", bg=WHITE, activebackground=WHITE,
            fg=TEXT, disabledforeground="#9A9A9A", selectcolor=WHITE, font=F(9), anchor="w",
            highlightthickness=0, bd=0, cursor="arrow")
        self.location_check.pack(anchor="w", padx=(20, 0), pady=(6, 0))
        self.location_hint = tk.Label(left, bg=WHITE, fg="#9A9A9A", font=F(8), justify="left",
                                      anchor="w", wraplength=320, text=self.LOCATION_TEXT)
        self.location_hint.pack(anchor="w", fill="x", padx=(20, 0), pady=(2, 0))
        # keep every hint inside the column, whatever the window width
        left.bind("<Configure>", lambda e: [
            lb.configure(wraplength=max(140, e.width - ind - 8))
            for lb, ind in ((self.exif_hint, 0), (self.resize_hint, 20),
                            (self.resize_note, 20), (self.location_hint, 20))])

        right_box, right = section(columns, "3.  Image conversion")
        right_box.grid(row=0, column=1, sticky="nsew")
        tk.Label(right, text="Convert to format", bg=WHITE, fg=TEXT_DIM, font=F(9)).pack(anchor="w")
        self.format_combo = ttk.Combobox(right, textvariable=self.output_format, state="readonly",
                                         values=list(CONVERSION_FORMATS.keys()), font=F(9))
        self.format_combo.pack(fill="x", pady=(3, 8))
        self.format_combo.bind("<<ComboboxSelected>>", self.on_format_changed)
        tk.Label(right, text="Quality", bg=WHITE, fg=TEXT_DIM, font=F(9)).pack(anchor="w")
        self.quality_combo = ttk.Combobox(right, textvariable=self.quality_mode, state="readonly",
                                          values=(QUALITY_HIGH, QUALITY_MAX), font=F(9))
        self.quality_combo.pack(fill="x", pady=(3, 6))
        quality_note = tk.Label(
            right, bg=WHITE, fg=TEXT_DIM, font=F(8), justify="left", anchor="w", wraplength=340,
            text="Maximum quality uses lossless WebP and quality 100 for JPEG, HEIC/HEIF and "
                 "AVIF. PNG and TIFF are always lossless. JPEG, GIF, HEIC/HEIF and AVIF "
                 "conversions may lose detail; transparency or animation may change.")
        quality_note.pack(anchor="w", fill="x")
        right.bind("<Configure>", lambda e: quality_note.configure(wraplength=max(140, e.width - 8)))

    # ------------------------------------------------------------- actions
    def effective_format(self):
        target, _ = CONVERSION_FORMATS[self.output_format.get()]
        return target or self.source_format

    def update_exif_hint(self):
        random_on = self.random_exif.get()
        fmt = self.effective_format()
        if random_on and fmt and fmt not in EXIF_FORMATS:
            self.exif_hint.configure(
                fg="#B05A00",
                text=f"{fmt} files cannot store EXIF. The copy will be saved without metadata. "
                     "Pick JPEG, PNG, WebP, HEIC or AVIF to write random EXIF.")
        else:
            self.exif_hint.configure(fg=TEXT_DIM, text=self.EXIF_TEXT)
        # The resolution option only makes sense together with random EXIF.
        self.downscale_check.configure(state="normal" if random_on else "disabled")
        self.location_check.configure(state="normal" if random_on else "disabled")
        if not random_on:
            self.downscale.set(False)
            self.location.set(False)
        self.update_resize_hint()
        self.update_location_hint()

    def update_location_hint(self):
        active = self.random_exif.get() and self.location.get()
        self.location_hint.configure(
            fg=OK_GREEN if active else ("#9A9A9A" if not self.random_exif.get() else TEXT_DIM),
            text=self.LOCATION_ON_TEXT if active else self.LOCATION_TEXT)

    def update_resize_hint(self):
        active = self.random_exif.get() and self.downscale.get()
        if active:
            if not self.resize_note.winfo_ismapped():
                self.resize_note.pack(anchor="w", fill="x", padx=(20, 0), pady=(1, 0),
                                      before=self.location_check)
        else:
            self.resize_note.pack_forget()
        if not active:
            self.resize_hint.configure(fg="#9A9A9A" if not self.random_exif.get() else TEXT_DIM,
                                       text=self.RESIZE_TEXT)
            return
        if self.source_size is None:
            self.resize_hint.configure(fg=TEXT_DIM, text="Select an image to see the new size.")
            return
        width, height = self.source_size
        new_size = downscale_size(width, height)
        if new_size:
            self.resize_hint.configure(
                fg=OK_GREEN, text=f"{width} x {height}   ->   {new_size[0]} x {new_size[1]}")
        else:
            self.resize_hint.configure(
                fg="#B05A00", text=f"{width} x {height}: too small, it will stay as it is.")

    def need_pillow(self):
        if Image is None:
            self.app.error("Pillow is not installed",
                           "OpenImage needs the Pillow package.\n\nInstall it with:  pip install pillow\n\n"
                           f"({PIL_ERROR})")
            return False
        return True

    def choose_image(self):
        if not self.need_pillow():
            return
        filename = filedialog.askopenfilename(
            parent=self.app.root, title="Select an image",
            filetypes=[("Supported images", IMAGE_TYPES), ("All files", "*.*")])
        if not filename:
            return
        path = Path(filename)
        try:
            with Image.open(path) as img:
                fmt = img.format or path.suffix.upper()
                dimensions = f"{img.width} x {img.height}"
                frames = getattr(img, "n_frames", 1)
                size = img.size
                # size as it is shown: phone photos are often stored sideways
                if normalize_format(fmt) not in ("HEIF", "AVIF") and safe_orientation(img) in (5, 6, 7, 8):
                    size = (size[1], size[0])
            self.source_path = path
            self.source_size = size
            self.source_format = normalize_format(fmt)
            self.file_info.set(f"{path.name}\n{fmt}  -  {dimensions}"
                               + (f"  -  {frames} frames" if frames > 1 else ""))
            self.output_format.set("Original format")
            self.output_name.set(random_filename(path.suffix or ".png"))
            self.status.set("Image selected. Choose the output options.")
            self.update_exif_hint()
        except Exception as exc:
            self.source_path = None
            self.source_format = None
            self.source_size = None
            self.file_info.set("No image selected")
            self.app.error("Cannot open image", f"Could not read image information:\n\n{exc}")

    def on_format_changed(self, _event=None):
        self.update_exif_hint()
        if not self.source_path:
            return
        choice = self.output_format.get()
        _, new_ext = CONVERSION_FORMATS[choice]
        if choice == "Original format":
            new_ext = self.source_path.suffix.lower() or ".png"
        old_name = self.output_name.get().strip()
        stem = Path(old_name).stem if old_name else random_filename(new_ext).rsplit(".", 1)[0]
        self.output_name.set(stem + new_ext)

    def choose_folder(self):
        folder = filedialog.askdirectory(
            parent=self.app.root, title="Choose output folder",
            initialdir=self.output_dir.get() or str(desktop_path()))
        if folder:
            self.output_dir.set(folder)

    def process_image(self):
        if not self.need_pillow():
            return
        if not self.source_path:
            self.app.info("Select an image", "Please select an image first.")
            return
        folder = Path(self.output_dir.get()).expanduser()
        if not folder.is_dir():
            self.app.error("Invalid folder", "Please choose an existing output folder.")
            return
        name = self.output_name.get().strip()
        if not name:
            self.app.error("Missing filename", "Please enter an output filename.")
            return

        choice = self.output_format.get()
        target_format, target_ext = CONVERSION_FORMATS[choice]
        if choice == "Original format":
            target_ext = self.source_path.suffix.lower() or ".png"
        stem = Path(name).stem
        if not stem:
            self.app.error("Invalid filename", "Please enter a valid output filename.")
            return
        name = stem + target_ext
        self.output_name.set(name)
        destination = folder / name
        if destination.exists() and destination.resolve() == self.source_path.resolve():
            self.app.error("Same file", "The output cannot overwrite the original image.")
            return
        if destination.exists() and not self.app.ask_yes_no(
                "Replace existing file?", f"{destination.name} already exists. Replace it?"):
            return

        # Work on a temporary file so a failed export never leaves a broken
        # image (or damages an existing file) at the destination.
        temp = destination.with_name(f".{destination.stem}.{secrets.token_hex(4)}.tmp")
        try:
            self.status.set("Processing image...")
            self.root.update_idletasks()
            request = (RandomExif(downscale=self.downscale.get(), location=self.location.get())
                       if self.random_exif.get() else None)
            notes, summary = export_clean_image(
                self.source_path, temp, target_format, self.quality_mode.get(), request)
            os.replace(temp, destination)
            self.status.set(f"Saved: {destination}")
            lines = [f"Saved file:\n{destination}"]
            if summary:
                lines.append(f"Random EXIF written:\n{summary}")
            if summary and request.result.location:
                lines.append("Random location (on land):\n" + format_location(*request.result.location))
            if request is not None and request.resized:
                lines.append("Resolution reduced:\n%d x %d  ->  %d x %d" % (
                    request.original_size + request.resized))
            elif request is None:
                lines.append("All metadata was removed.")
            lines += [f"Note: {note}" for note in notes]
            self.app.info("Finished", "\n\n".join(lines))
        except Exception as exc:
            self.status.set("Processing failed.")
            log_path = DATA_DIR / "openimage_error.log"
            try:
                DATA_DIR.mkdir(parents=True, exist_ok=True)
                log_path.write_text(traceback.format_exc(), encoding="utf-8")
                log_info = f"A detailed error log was saved here:\n{log_path}"
            except OSError:
                log_info = "(The error log could not be written.)"
            self.app.error("The image could not be processed",
                           f"{type(exc).__name__}: {exc}\n\n{log_info}")
        finally:
            try:
                if temp.exists():
                    temp.unlink()
            except OSError:
                pass


def keycap(parent, text):
    cap = tk.Frame(parent, bg="#A9B3C2")
    tk.Label(cap, text=text, bg="#F6F8FB", fg="#25364F", font=F(8, True),
             padx=8, pady=3, width=14).pack(padx=1, pady=1)
    return cap


class NuMousePage:
    """Status + controls of the background NuMouse helper."""

    def __init__(self, app, parent, tool):
        self.app = app
        self.tool = tool
        entry = app.procs.get(tool["name"])
        pid = entry["proc"].pid if entry else "-"

        outer = tk.Frame(parent, bg=WHITE)
        outer.pack(fill="both", expand=True, padx=26, pady=(18, 10))
        page_heading(outer, tool["name"], tool["description"])

        box, body = section(outer, "Status")
        box.pack(fill="x", pady=(16, 0))
        row = tk.Frame(body, bg=WHITE)
        row.pack(fill="x")
        IconBox(row, kind="running", size=16, bg=WHITE).pack(side="left")
        tk.Label(row, text="Running", bg=WHITE, fg=OK_GREEN, font=F(10, True)).pack(side="left", padx=(6, 0))
        tk.Label(row, text=f"Process ID {pid}", bg=WHITE, fg=TEXT_DIM, font=F(8)).pack(side="right")
        note = tk.Label(body, bg=WHITE, fg=TEXT_DIM, font=F(9), justify="left", anchor="w",
                        text="It keeps running in the background when you go back to the tool list. "
                             "NumLock must be on. Press Num - to switch mouse control on or off.")
        note.pack(anchor="w", fill="x", pady=(6, 0))
        body.bind("<Configure>", lambda e, lb=note: lb.configure(wraplength=max(200, e.width - 8)))

        box, body = section(outer, "Controls")
        box.pack(fill="x", pady=(16, 0))
        for key, description in tool.get("details", []):
            line = tk.Frame(body, bg=WHITE)
            line.pack(fill="x", pady=3)
            keycap(line, key).pack(side="left")
            tk.Label(line, text=description, bg=WHITE, fg=TEXT, font=F(9)).pack(side="left", padx=12)

        buttons = tk.Frame(outer, bg=WHITE)
        buttons.pack(fill="x", pady=(20, 0))
        AeroButton(buttons, f"Stop {tool['name']}", lambda: app.stop_and_home(tool), width=130).pack(side="left")
        AeroButton(buttons, "Back to tools", app.go_home, width=110, default=True).pack(side="left", padx=(8, 0))


# ===========================================================================
#  SECTION 6 - THE HUB
# ===========================================================================

TOOLS = [
    {
        "name": "NuMouse",
        "description": "Control your mouse cursor using the keyboard numpad.",
        "kind": "process",
        "icon": "mouse",
        "background": True,          # keeps running when you leave its page
        "details": [
            ("NUM -", "Toggle mouse control on / off"),
            ("8 / 2 / 4 / 6", "Move the cursor"),
            ("7 / 9 / 5", "Hold left / right / middle mouse button"),
            ("0", "Move slowly"),
            ("3 / ,", "Scroll up / down"),
        ],
    },
    {
        "name": "OpenImage",
        "description": "Remove EXIF and embedded metadata from images, or write random phone EXIF.",
        "kind": "embedded",
        "icon": "image",
    },
]

NAV_ITEMS = [("all", "All tools", "all"), ("builtin", "Built-in tools", "tools"),
             ("apps", "Added apps", "apps"), ("running", "Running now", "running")]
MODE_TITLES = {"all": "All tools", "builtin": "Built-in tools",
               "apps": "Added apps", "running": "Running now"}

SEL_BG, HOT_BG = "#DCEBFC", "#EEF5FD"
DETAILS_BG = "#F2F6FB"


# ----------------------------- added apps storage ------------------------------

def load_apps():
    if not APPS_FILE.is_file():
        return []
    try:
        data = json.loads(APPS_FILE.read_text(encoding="utf-8"))
        apps = []
        for item in data:
            if isinstance(item, dict) and item.get("path"):
                apps.append({
                    "id": str(item.get("id") or uuid.uuid4().hex[:12]),
                    "name": str(item.get("name") or Path(item["path"]).stem),
                    "path": str(item["path"]),
                    "icon": item.get("icon") or None,
                })
        return apps
    except (OSError, ValueError, TypeError):
        try:                              # keep a copy instead of overwriting it
            APPS_FILE.replace(APPS_FILE.with_suffix(".json.bak"))
        except OSError:
            pass
        return []


def save_apps(apps):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    temp = APPS_FILE.with_suffix(".json.tmp")
    temp.write_text(json.dumps(apps, indent=2, ensure_ascii=False), encoding="utf-8")
    os.replace(temp, APPS_FILE)


def extract_exe_icon(exe_path, out_png):
    """Save the icon of an .exe as a PNG (Windows). Returns True on success."""
    if not IS_WINDOWS:
        return False
    script = (
        "Add-Type -AssemblyName System.Drawing;"
        "$ic=[System.Drawing.Icon]::ExtractAssociatedIcon($env:UH_SRC);"
        "if($ic -eq $null){exit 2};"
        "$bmp=$ic.ToBitmap();"
        "$bmp.Save($env:UH_OUT,[System.Drawing.Imaging.ImageFormat]::Png);"
        "$bmp.Dispose();$ic.Dispose()"
    )
    env = os.environ.copy()
    env["UH_SRC"] = str(exe_path)           # passed via environment: no quoting issues
    env["UH_OUT"] = str(out_png)
    try:
        subprocess.run(
            ["powershell", "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass",
             "-Command", script],
            env=env, creationflags=NO_WINDOW, timeout=25, stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except (OSError, subprocess.SubprocessError):
        return False
    try:
        return Path(out_png).is_file() and Path(out_png).stat().st_size > 0
    except OSError:
        return False


def launch_external(path):
    """Start an external program in its own folder (like Steam's 'Play')."""
    path = Path(path)
    workdir = str(path.parent)
    try:
        subprocess.Popen([str(path)], cwd=workdir, close_fds=True)
    except OSError as exc:
        # WinError 740: the program needs administrator rights. ShellExecute
        # shows the normal UAC prompt for it.
        if IS_WINDOWS and getattr(exc, "winerror", None) == 740:
            if sys.version_info >= (3, 10):
                os.startfile(str(path), cwd=workdir)
            else:
                os.startfile(str(path))
        else:
            raise


def bind_tree(widget, sequence, func, skip=(AeroButton,)):
    """Bind an event on a widget and all its descendants."""
    if not isinstance(widget, skip):
        widget.bind(sequence, func, add="+")
    for child in widget.winfo_children():
        bind_tree(child, sequence, func, skip)


class HubApp:
    NAV_WIDTH = 200

    def __init__(self, root):
        self.root = root
        root.title(APP_NAME)
        width, height = 940, 660
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        width, height = min(width, sw - 40), min(height, sh - 80)
        root.geometry("%dx%d+%d+%d" % (width, height, (sw - width) // 2, max(10, (sh - height) // 3)))
        self.window = AeroWindow(root, APP_NAME, taskbar=True, min_size=(780, 620),
                                 on_close=self.on_close)

        self.procs = {}                  # tool name -> {"proc": Popen, "log_path": Path}
        self.current_tool = None
        self.forward_target = None
        self.custom_apps = load_apps()
        self.photos = {}                 # keeps PhotoImages alive
        self.filter_mode = "all"
        self.selected_id = None
        self.rows = {}
        self.nav = self.content = self.details_body = self.scroll = None
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self.on_search())

        self.show_home()
        root.after(600, self.poll_processes)
        root.after(150, root.focus_force)

    # ------------------------------------------------------------- dialogs
    def info(self, heading, text=""):
        return aero_dialog(self.root, heading, text, "info", ("OK",))

    def warn(self, heading, text=""):
        return aero_dialog(self.root, heading, text, "warning", ("OK",))

    def error(self, heading, text=""):
        return aero_dialog(self.root, heading, text, "error", ("OK",))

    def ask_yes_no(self, heading, text=""):
        return aero_dialog(self.root, heading, text, "question", ("Yes", "No"),
                           default=0, cancel=1) == 0

    # ----------------------------------------------------------- navigation
    def clear_client(self):
        for child in self.window.client.winfo_children():
            child.destroy()
        self.scroll = self.nav = self.content = self.details_body = None
        self.rows = {}

    def build_address_row(self, crumbs, search=False, can_back=False):
        glass = self.window.glass
        for child in glass.winfo_children():
            child.destroy()
        row = tk.Frame(glass, bg=GLASS)
        row.pack(fill="x", padx=8, pady=(5, 8))
        OrbButton(row, "back", self.go_back, enabled=can_back).pack(side="left")
        OrbButton(row, "fwd", self.go_forward,
                  enabled=self.forward_target is not None).pack(side="left", padx=(3, 8))
        if search:
            AeroEntry(row, textvariable=self.search_var, placeholder="Search tools",
                      width=24).pack(side="right", padx=(8, 0))
        bar = tk.Frame(row, bg=WHITE, highlightthickness=1, highlightbackground="#8FA0B8")
        bar.pack(side="left", fill="x", expand=True)
        inner = tk.Frame(bar, bg=WHITE)
        inner.pack(fill="x", padx=6, pady=4)
        IconBox(inner, kind="hub", size=16, bg=WHITE).pack(side="left", padx=(0, 6))
        for index, crumb in enumerate(crumbs):
            if index:
                tk.Label(inner, text="\u25B8", bg=WHITE, fg="#6B7B90", font=F(8)).pack(side="left", padx=4)
            label = tk.Label(inner, text=crumb, bg=WHITE, fg=TEXT, font=F(9))
            label.pack(side="left")
            if index == 0 and self.current_tool is not None:
                label.configure(cursor="hand2")
                label.bind("<Button-1>", lambda e: self.go_home())
                label.bind("<Enter>", lambda e, w=label: w.configure(fg=LINK))
                label.bind("<Leave>", lambda e, w=label: w.configure(fg=TEXT))

    def go_back(self):
        if self.current_tool is not None:
            self.go_home()

    def go_forward(self):
        tool, self.forward_target = self.forward_target, None
        if tool is not None:
            self.open_tool(tool)

    def go_home(self):
        tool = self.current_tool
        # Background tools stay alive; other process tools stop with their page.
        if tool and tool["kind"] == "process" and not tool.get("background"):
            self.stop_process(tool["name"])
        self.forward_target = tool
        self.show_home()

    # ------------------------------------------------------------------ home
    def show_home(self):
        self.current_tool = None
        self.clear_client()
        self.window.set_title(APP_NAME)
        self.build_address_row(["UltimateHub", "Tools"], search=True, can_back=False)
        page = WallpaperCanvas(self.window.client)
        page.pack(fill="both", expand=True)

        # bottom pane first, so it always stays visible
        bottom = card(page, DETAILS_BG)
        bottom.pack(side="bottom", fill="x", padx=10, pady=(0, 10))
        strip = tk.Frame(bottom, bg=DETAILS_BG, height=88)
        strip.pack(fill="x")
        strip.pack_propagate(False)
        add_cell = tk.Frame(strip, bg=DETAILS_BG, width=self.NAV_WIDTH)
        add_cell.pack(side="left", fill="y")
        add_cell.pack_propagate(False)
        AeroButton(add_cell, "+  Add app", self.add_app, width=120, height=27,
                   font=F(9, True), bg=DETAILS_BG).place(relx=0.5, rely=0.5, anchor="center")
        tk.Frame(strip, bg="#D5DFEC", width=1).pack(side="left", fill="y", pady=8)
        self.details_body = tk.Frame(strip, bg=DETAILS_BG)
        self.details_body.pack(side="left", fill="both", expand=True, padx=16)

        self.nav = card(page, NAV_BG)
        self.nav.configure(width=self.NAV_WIDTH)
        self.nav.pack(side="left", fill="y", padx=(10, 0), pady=10)
        self.nav.pack_propagate(False)
        self.content = card(page, WHITE)
        self.content.pack(side="left", fill="both", expand=True, padx=10, pady=10)

        self.render_nav()
        self.render_content()
        self.render_details()

    # ---- data ----------------------------------------------------------------
    def search_text(self):
        return self.search_var.get().strip().casefold()

    def counts(self):
        running = sum(1 for tool in TOOLS if self.is_running(tool))
        return {"all": len(TOOLS) + len(self.custom_apps), "builtin": len(TOOLS),
                "apps": len(self.custom_apps), "running": running}

    def visible_items(self):
        query, mode = self.search_text(), self.filter_mode
        items = []
        if mode in ("all", "builtin", "running"):
            for tool in TOOLS:
                running = self.is_running(tool)
                if mode == "running" and not running:
                    continue
                if query and query not in tool["name"].casefold() \
                        and query not in tool["description"].casefold():
                    continue
                items.append({"id": "tool:" + tool["name"], "kind": "tool", "tool": tool,
                              "running": running})
        if mode in ("all", "apps"):
            for app in self.custom_apps:
                if query and query not in app["name"].casefold() \
                        and query not in app["path"].casefold():
                    continue
                items.append({"id": "app:" + app["id"], "kind": "app", "app": app})
        return items

    def load_photo(self, icon_file):
        if not icon_file:
            return None
        path = ICON_DIR / icon_file
        key = str(path)
        if key in self.photos:
            return self.photos[key]
        if not path.is_file():
            return None
        try:
            image = tk.PhotoImage(master=self.root, file=key)
            if image.width() > 40 or image.height() > 40:
                image = image.subsample(max(1, -(-max(image.width(), image.height()) // 40)))
        except tk.TclError:
            return None
        self.photos[key] = image
        return image

    # ---- navigation pane --------------------------------------------------------
    def render_nav(self):
        if self.nav is None:
            return
        for child in self.nav.winfo_children():
            child.destroy()
        tk.Label(self.nav, text="Library", bg=NAV_BG, fg=HEADING, font=F(9, True),
                 anchor="w").pack(fill="x", padx=14, pady=(14, 6))
        counts = self.counts()
        for key, label, icon in NAV_ITEMS:
            selected = key == self.filter_mode
            bg = SEL_BG if selected else NAV_BG
            border = SEL_BORDER if selected else NAV_BG
            item = tk.Frame(self.nav, bg=bg, highlightthickness=1, highlightbackground=border)
            item.pack(fill="x", padx=8, pady=1)
            IconBox(item, kind=icon, size=16, bg=bg).pack(side="left", padx=(8, 8), pady=5)
            tk.Label(item, text=label, bg=bg, fg=TEXT, font=F(9), anchor="w").pack(side="left")
            tk.Label(item, text=str(counts[key]), bg=bg, fg=TEXT_DIM, font=F(8)).pack(side="right", padx=8)
            self._wire_nav(item, key, selected)

    def _wire_nav(self, item, key, selected):
        def hover(on):
            if not selected and item.winfo_exists():
                color, border = (HOT_BG, HOT_BORDER) if on else (NAV_BG, NAV_BG)
                item.configure(bg=color, highlightbackground=border)
                set_bg_recursive(item, color)

        bind_tree(item, "<Enter>", lambda e: hover(True), skip=())
        bind_tree(item, "<Leave>", lambda e: self.root.after_idle(
            lambda: hover(self.pointer_inside(item))), skip=())
        bind_tree(item, "<Button-1>", lambda e, k=key: self.set_filter(k), skip=())

    def set_filter(self, mode):
        self.filter_mode = mode
        self.render_nav()
        self.render_content()
        self.render_details()

    # ---- list ---------------------------------------------------------------------
    def on_search(self):
        if self.current_tool is None and self.content is not None and self.content.winfo_exists():
            self.render_content()
            self.render_details()

    def refresh_home(self):
        if self.current_tool is None and self.content is not None and self.content.winfo_exists():
            self.render_nav()
            self.render_content()
            self.render_details()

    def render_content(self):
        if self.content is None:
            return
        for child in self.content.winfo_children():
            child.destroy()
        self.rows = {}
        items = self.visible_items()
        if self.selected_id and not any(i["id"] == self.selected_id for i in items):
            self.selected_id = None

        head = tk.Frame(self.content, bg=WHITE)
        head.pack(fill="x", padx=18, pady=(14, 4))
        tk.Label(head, text=MODE_TITLES[self.filter_mode], bg=WHITE, fg=HEADING,
                 font=F(14)).pack(side="left")
        tk.Label(head, text=f"{len(items)} item{'s' if len(items) != 1 else ''}", bg=WHITE,
                 fg=TEXT_DIM, font=F(9)).pack(side="left", padx=(10, 0), pady=(5, 0))

        self.scroll = ScrollFrame(self.content, WHITE)
        self.scroll.pack(fill="both", expand=True)
        area = self.scroll.inner
        if not items:
            tk.Label(area, text="No items found.", bg=WHITE, fg=TEXT_DIM,
                     font=F(10)).pack(anchor="w", padx=22, pady=18)
            return
        last_kind = None
        for item in items:
            if self.filter_mode == "all" and item["kind"] != last_kind:
                title = "Built-in tools" if item["kind"] == "tool" else "Added apps"
                gh = tk.Frame(area, bg=WHITE)
                gh.pack(fill="x", padx=18, pady=(10, 2))
                tk.Label(gh, text=title, bg=WHITE, fg=HEADING, font=F(9)).pack(side="left")
                tk.Frame(gh, bg="#D5DFE5", height=1).pack(side="left", fill="x", expand=True,
                                                          padx=(8, 0), pady=(3, 0))
            last_kind = item["kind"]
            self.build_row(area, item)
        for item in items:
            self.style_row(item["id"])

    def build_row(self, parent, item):
        row = tk.Frame(parent, bg=WHITE, highlightthickness=1, highlightbackground=WHITE)
        row.pack(fill="x", padx=(14, 14), pady=1)
        inside = tk.Frame(row, bg=WHITE)
        inside.pack(fill="x", padx=10, pady=8)

        if item["kind"] == "tool":
            tool = item["tool"]
            IconBox(inside, kind=tool["icon"], size=40, bg=WHITE).pack(side="left", padx=(0, 12))
            running = item["running"]
            # right-side buttons first; the last one packed sits left of the others
            if running:
                AeroButton(inside, "Stop", lambda t=tool: self.stop_tool(t), width=70).pack(
                    side="right", padx=(8, 0))
            AeroButton(inside, "Open", lambda t=tool: self.open_tool(t), width=78,
                       default=True).pack(side="right", padx=(8, 0))
            name, description, activate = tool["name"], tool["description"], (lambda t=tool: self.open_tool(t))
        else:
            app = item["app"]
            photo = self.load_photo(app.get("icon"))
            IconBox(inside, size=40, image=photo, letter=app["name"][:1], bg=WHITE).pack(
                side="left", padx=(0, 12))
            AeroButton(inside, "Delete", lambda a=app: self.delete_app(a), width=70).pack(
                side="right", padx=(8, 0))
            AeroButton(inside, "Run", lambda a=app: self.run_app(a), width=78,
                       default=True).pack(side="right", padx=(8, 0))
            missing = not Path(app["path"]).is_file()
            name = app["name"]
            description = ("File not found: " if missing else "") + app["path"]
            activate = (lambda a=app: self.run_app(a))

        text = tk.Frame(inside, bg=WHITE)
        text.pack(side="left", fill="x", expand=True)
        title_row = tk.Frame(text, bg=WHITE)
        title_row.pack(anchor="w")
        tk.Label(title_row, text=name, bg=WHITE, fg=TEXT, font=F(11, True)).pack(side="left")
        if item["kind"] == "tool" and item["running"]:
            tk.Label(title_row, text="\u25CF  Running", bg=WHITE, fg=OK_GREEN,
                     font=F(8, True)).pack(side="left", padx=(10, 0))
        desc = tk.Label(text, text=description, bg=WHITE, justify="left", anchor="w", font=F(9),
                        fg=("#B00020" if description.startswith("File not found") else TEXT_DIM))
        desc.pack(anchor="w", pady=(2, 0))
        text.bind("<Configure>", lambda e, lb=desc: lb.configure(wraplength=max(120, e.width - 6)))

        self.rows[item["id"]] = row
        iid = item["id"]
        bind_tree(row, "<Enter>", lambda e, i=iid: self.style_row(i))
        bind_tree(row, "<Leave>", lambda e, i=iid: self.root.after_idle(lambda: self.style_row(i)))
        bind_tree(row, "<Button-1>", lambda e, i=iid: self.select(i))
        bind_tree(row, "<Double-Button-1>", lambda e, f=activate: f())

    def pointer_inside(self, widget):
        try:
            under = widget.winfo_containing(self.root.winfo_pointerx(), self.root.winfo_pointery())
        except (tk.TclError, KeyError):
            return False
        while under is not None:
            if under is widget:
                return True
            under = under.master
        return False

    def style_row(self, item_id):
        row = self.rows.get(item_id)
        if row is None or not row.winfo_exists():
            return
        if item_id == self.selected_id:
            bg, border = SEL_BG, SEL_BORDER
        elif self.pointer_inside(row):
            bg, border = HOT_BG, HOT_BORDER
        else:
            bg, border = WHITE, WHITE
        row.configure(bg=bg, highlightbackground=border)
        set_bg_recursive(row, bg)

    def select(self, item_id):
        previous, self.selected_id = self.selected_id, item_id
        for iid in (previous, item_id):
            if iid:
                self.style_row(iid)
        self.render_details()

    # ---- details pane -------------------------------------------------------------
    def render_details(self):
        if self.details_body is None or not self.details_body.winfo_exists():
            return
        for child in self.details_body.winfo_children():
            child.destroy()
        item = next((i for i in self.visible_items() if i["id"] == self.selected_id), None)
        body = self.details_body
        if item is None:
            count = len(self.visible_items())
            tk.Label(body, text=f"{count} item{'s' if count != 1 else ''}", bg=DETAILS_BG,
                     fg=TEXT, font=F(10, True)).pack(anchor="w", pady=(20, 0))
            tk.Label(body, text="Select an item to see its details. Double-click to open or run it.",
                     bg=DETAILS_BG, fg=TEXT_DIM, font=F(9)).pack(anchor="w", pady=(2, 0))
            return
        if item["kind"] == "tool":
            tool = item["tool"]
            icon = IconBox(body, kind=tool["icon"], size=48, bg=DETAILS_BG)
            title, kind_text = tool["name"], "Built-in tool"
            entry = self.procs.get(tool["name"])
            if item["running"] and entry:
                status = f"Status: Running  (process ID {entry['proc'].pid})"
            elif tool["kind"] == "process":
                status = "Status: Stopped"
            else:
                status = "Status: Ready"
            extra = tool["description"]
        else:
            app = item["app"]
            icon = IconBox(body, size=48, image=self.load_photo(app.get("icon")),
                           letter=app["name"][:1], bg=DETAILS_BG)
            title, kind_text = app["name"], "Added application"
            status = ("File not found" if not Path(app["path"]).is_file() else "Location: " + app["path"])
            extra = ""
        icon.pack(side="left", pady=18, padx=(0, 14))
        lines = tk.Frame(body, bg=DETAILS_BG)
        lines.pack(side="left", fill="both", expand=True, pady=14)
        tk.Label(lines, text=title, bg=DETAILS_BG, fg=TEXT, font=F(11, True)).pack(anchor="w")
        tk.Label(lines, text=kind_text, bg=DETAILS_BG, fg=TEXT_DIM, font=F(9)).pack(anchor="w")
        tk.Label(lines, text=status, bg=DETAILS_BG, fg=OK_GREEN if "Running" in status else TEXT,
                 font=F(9), anchor="w", justify="left").pack(anchor="w")
        if extra:
            tk.Label(lines, text=extra, bg=DETAILS_BG, fg=TEXT_DIM, font=F(9),
                     anchor="w", justify="left").pack(anchor="w")

    # -------------------------------------------------------------- added apps
    def add_app(self):
        filename = filedialog.askopenfilename(
            parent=self.root, title="Select an application", filetypes=[("Applications", "*.exe")])
        if not filename:
            return
        path = Path(filename)
        if path.suffix.lower() != ".exe":
            self.error("Not an application", "Please select an .exe file.")
            return
        wanted = os.path.normcase(os.path.abspath(str(path)))
        for app in self.custom_apps:
            if os.path.normcase(os.path.abspath(app["path"])) == wanted:
                self.info("Already added", f"{app['name']} is already in UltimateHub.")
                return

        app_id = uuid.uuid4().hex[:12]
        icon_name = f"{app_id}.png"
        self.root.configure(cursor="watch")
        self.root.update_idletasks()
        try:
            ICON_DIR.mkdir(parents=True, exist_ok=True)
            has_icon = extract_exe_icon(path, ICON_DIR / icon_name)
        except OSError:
            has_icon = False
        finally:
            self.root.configure(cursor="")

        entry = {"id": app_id, "name": path.stem, "path": str(path),
                 "icon": icon_name if has_icon else None}
        previous = list(self.custom_apps)
        self.custom_apps.append(entry)
        try:
            save_apps(self.custom_apps)
        except OSError as exc:
            self.custom_apps = previous
            self.error("Could not save", f"The app list could not be saved:\n{exc}")
            return

        # Show the new app: leave any search / filter that would hide it.
        self.filter_mode = "all" if self.filter_mode in ("builtin", "running") else self.filter_mode
        self.selected_id = "app:" + app_id
        if self.search_var.get():
            self.search_var.set("")          # the trace re-renders the list
        self.refresh_home()
        if self.scroll is not None:
            self.scroll.scroll_to_end()

    def run_app(self, app):
        path = Path(app["path"])
        if not path.is_file():
            self.error("File not found",
                       f"{path}\n\nThe file was moved or deleted. Delete this entry and add the app again.")
            return
        try:
            launch_external(path)
        except Exception as exc:
            self.error("Could not run app", f"{app['name']} could not be started:\n{exc}")

    def delete_app(self, app):
        if not self.ask_yes_no(f"Remove {app['name']} from UltimateHub?",
                               "The program itself is not deleted from your computer."):
            return
        previous = list(self.custom_apps)
        self.custom_apps = [a for a in self.custom_apps if a["id"] != app["id"]]
        try:
            save_apps(self.custom_apps)
        except OSError as exc:
            self.custom_apps = previous
            self.error("Could not save", f"The app list could not be saved:\n{exc}")
            return
        if app.get("icon"):
            self.photos.pop(str(ICON_DIR / app["icon"]), None)
            try:
                (ICON_DIR / app["icon"]).unlink()
            except OSError:
                pass
        if self.selected_id == "app:" + app["id"]:
            self.selected_id = None
        self.refresh_home()

    # -------------------------------------------------------------- tool pages
    def open_tool(self, tool):
        self.forward_target = None
        if tool["kind"] == "embedded":
            self.show_tool_page(tool)
            return
        if not self.is_running(tool):          # reuse a running instance
            if not self.start_process(tool):
                return
        self.show_tool_page(tool)

    def show_tool_page(self, tool):
        self.current_tool = tool
        self.clear_client()
        self.window.set_title(f"{tool['name']} - {APP_NAME}")
        self.build_address_row(["UltimateHub", tool["name"]], search=False, can_back=True)
        try:
            wall = WallpaperCanvas(self.window.client)
            wall.pack(fill="both", expand=True)
            panel = card(wall, WHITE)
            panel.pack(fill="both", expand=True, padx=14, pady=14)
            if tool["kind"] == "embedded":
                OpenImagePage(self, panel)
            else:
                NuMousePage(self, panel, tool)
        except Exception as exc:
            self.current_tool = None
            self.show_home()
            self.error("Could not open tool", f"{tool['name']} could not be loaded:\n{exc}")

    # ------------------------------------------------------- background tools
    def is_running(self, tool):
        entry = self.procs.get(tool["name"])
        return bool(entry and entry["proc"].poll() is None)

    def start_process(self, tool):
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        log_path = DATA_DIR / f"{tool['name'].lower()}.log"
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        try:
            with open(log_path, "w", encoding="utf-8") as log_file:
                proc = subprocess.Popen(
                    # --managed: the tool exits when we send "quit" or when
                    # this pipe closes (e.g. the Hub crashes).
                    SELF_CMD + ["--numouse", "--managed"],
                    cwd=str(BASE_DIR), env=env, stdin=subprocess.PIPE,
                    stdout=log_file, stderr=subprocess.STDOUT, creationflags=NO_WINDOW)
        except Exception as exc:
            self.error("Could not launch tool", f"An error occurred while starting {tool['name']}:\n{exc}")
            return False
        self.procs[tool["name"]] = {"proc": proc, "log_path": log_path}
        return True

    @staticmethod
    def close_stdin(proc):
        try:
            if proc.stdin:
                proc.stdin.close()
        except (OSError, ValueError):
            pass

    def stop_process(self, name):
        """Ask politely first (so the tool can release held mouse buttons),
        then terminate, then kill."""
        entry = self.procs.pop(name, None)
        if not entry:
            return
        proc = entry["proc"]
        if proc.poll() is None:
            try:
                proc.stdin.write(b"quit\n")
                proc.stdin.flush()
            except (OSError, ValueError):
                pass
            self.close_stdin(proc)
            try:
                proc.wait(timeout=2.5)
            except subprocess.TimeoutExpired:
                proc.terminate()
                try:
                    proc.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    try:
                        proc.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        pass
        else:
            self.close_stdin(proc)

    def stop_all_processes(self):
        for name in list(self.procs):
            self.stop_process(name)

    def stop_tool(self, tool):
        """Stop button on a list row."""
        self.stop_process(tool["name"])
        self.refresh_home()

    def stop_and_home(self, tool):
        """Stop button inside the tool page."""
        self.stop_process(tool["name"])
        self.forward_target = None
        self.show_home()

    @staticmethod
    def read_log_tail(path, limit=700):
        try:
            text = Path(path).read_text(encoding="utf-8", errors="replace").strip()
        except OSError:
            return ""
        return text[-limit:]

    def poll_processes(self):
        """Detects tools that exited on their own (crash, missing package...)."""
        try:
            for name, entry in list(self.procs.items()):
                code = entry["proc"].poll()
                if code is None:
                    continue
                self.procs.pop(name, None)
                self.close_stdin(entry["proc"])
                viewing = bool(self.current_tool and self.current_tool["name"] == name)
                if viewing:
                    self.show_home()
                else:
                    self.refresh_home()
                detail = self.read_log_tail(entry["log_path"])
                message = f"Exit code: {code}\n\n"
                message += (f"Last output:\n{detail}" if detail
                            else "Check that all required packages are installed.")
                self.warn(f"{name} stopped unexpectedly", message)
        finally:
            try:
                self.root.after(600, self.poll_processes)
            except tk.TclError:
                pass

    def on_close(self):
        self.stop_all_processes()
        self.root.destroy()


def main():
    if "--numouse" in sys.argv:                  # background helper process
        run_numouse(managed="--managed" in sys.argv)
        return
    root = tk.Tk()
    HubApp(root)
    root.mainloop()


# --- embedded geo data: 0.1 degree land mask (zlib, packed bits) and a 0.5 degree
# --- population weight grid (zlib, uint8, w = exp(q / 20) - 1). Generated once.
LAND_MASK_B64 = (
    "eNrsvV+MH8t159c9PZc9skbsERSs6TXNHq0M2AGC3HEExNSaZo0tI9oHI9fA7kPypMk6iB7yYCp6EA3TrObyRlRgwaMgD9Ei"
    "jucGAZKHPKyDfVgjMcKmeG1eI1qPNg4CG3HCpqgVBcTxbYrKskfs6cqv//36X3V3dXdVd9VvzhfCvbrD4e/XXZ+qU+ecOlWl"
    "aSAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAg"
    "EAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAI"
    "BAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQC"
    "gUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFA"
    "IBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQ"
    "CAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgE"
    "AoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQCAQCgUAgEAgEAoFAIBAIBAKB"
    "QCAQCAQCgUAgEAgEAoFAIBAIBAKBQCAQJ21DE4BAS8p5bwsaQWUZv6J/yoFmUFqPCLSB2lZU10xoBZVlaxp5+R60g6rSt5+S"
    "lTyGXwWHR0rt/rMTRoBga+XUf/FTT1YEmZzRy9BaMmrvJ36JkJDpV69Ca8kpk5CA6RddaCspYwkNEcLExoS4X0ZtbeuraRDa"
    "QV397I7FOg2CZNShExP0oSFU1c6BtmUzRoMgGWV59p+YjNEgSEZd3l+5oeDIKKxLW7ar2RE0hLr6yAkQVFu7J+4tG1xRheP5"
    "Q8tlzMiAJJUOBFXWvuZqng3hoMJ6izhHNqRkFNZVyzsyYAyq7IoaZ54G86C62t7WjFDzHGgJZQkeaSZxD6Eh1NV/aBHyBppB"
    "YRGbwMqE2jpdEbwHvqjCiqt9y77oDjSJYkKkYkavXIImUUwWqVSq/djWEbSJUjqMCZaWB8174NYoRvCYVGoNddcGhErpfhxN"
    "lBLbuo++Aa2ikjxMKpsm3gpvQqMopeeE1La93LgOraKQ9DcNgiC19AoIqq23YoCwRK+wbCCotrY+QliPsQBJ6snAGFRcH8FA"
    "UGkjql/5RSCotrYDiCbU1uXbGAgqrbefPSdwDoLC+iXT0zCcRaJ0RB9vwYaAUGEZL5KA8H1oCVVlvk4InjrQFIoGhJ9OAJKn"
    "LrSFmrq0S16SWsEoSCV95TcDXTWC0NnK2jYCW7XVic8CtrIVtUOiGsFfB2wl/TufJcoRRICtpMufU4/gDShJLunf/IJ6BDUd"
    "CJbG4G9kBBVaITwEbCXtYiCotq48zAjC+pKqsjKCsL6kqhAQVFofi297IVAyqrLWBKFcTVHZOUE4p1lJbWk3bZgI1dYfrp1R"
    "FxpDTf0GTISKiwBBtXWYp9WgbltR7RIgqLYzehUIKq6fWhOE3LbijgwQBIKgRYSBoOKywJNRneA5BPTsMhwJCUawPjgg+JLu"
    "ibY1RLKZ0AE+KhLcWRG0YXFJYYJxmcwxeKIKy7Rfkf0jOI+EXXckex6dvCQPNXBFBwRf0gX0ASYPgOCAWUc2j88OMfkQggnm"
    "eFC+hjI9BOEge39/IJ/DcOm7J0BwwCwoH8F/+z/CkFRjt1hShl1AcIAVlTJ5ZcPa0hBHRr662p1k40RkA0FVCd5LrGhow7YJ"
    "VoLS+XzXE4IIMtssktJj2EoIYlhdUpXgV5N5MISNL8oS3LWh0Eltgts27AAdFjzLlpTZN/JatacAiCl4jqS0DGBG2WTJSHB9"
    "qhOYUTUJ3t5FQHCQwZKund5aH4UAEWGvdCl7ug1HIQxzGqR7qIdwqhO7kIQEdQJjcAjBU+lmm/WxXDAGmaacP5WupwPBYa31"
    "pw9lS8oYQHCI8J8+jKQlCPMgixl981C2hgJPZpgZPTsh0XtAUOWI8ES2DLIO82Bde53xxEPZsjIGHI1X01tBdzwhL0HYQphN"
    "dWFP9CUXwTsaEKwzCnp6vGQEi3kQlpdSvX3W4zfI5cmg0qlO4IymQft5d4tJtg53s0TQAXpJvNDdEJZkXvu1giAUyuRmUutx"
    "ZQK5CBaejAERYUIw+tUeV0YqglcLgiEQZHE2ZXNlrpZufTEgpo8D+j5C0hF8ez0I78EYXGm7L67CcsVd17R3Cl8UCKZjrI+g"
    "VKUytlucEasBwXSeIyoFhJZjFdHEIfBLE8V9BF05CUJeNI/3egnKZKysYh4EgmuCnVbSlm0hDi5eqvXpvgyxLVtTgRVtAOom"
    "KFtSJvgZIFif5roJ6rIR/DJkthuzitsTMMo0DxrnsEY/lCBeETySKvoBgtUR1kvwha/J01hG+BBq1WoE/2kPQfTYMeSZcszQ"
    "BoJVP8U3+sagq5mRRARRQRC7QFAnztZJzxh0V5OPPFY0Wkf0q74HU6Gmr0aXxUDQkdCT8W24u2elmF43npvxSHXlIfjh2hfF"
    "UK7GpN3Y35GGoJ5eGAIFhwO0HRP05CFYEeBhjft9OQlC4T0zwVAegm+AoOIEH4MVVZqgViUInkyiw36C8nR28GRaYsK+ZpPm"
    "YW0gWJlVnPwffQ6gNOYKVQi6QDD+R++vGUBQaoJMrSYNQRsIjvMepCFoVQh6AIctBpOWIIxBZsOlyUkQ4kFm50FSggCHmaAD"
    "BBWWJdOEAwRHyJCpMKwaTTjfADw6w+/gQJ5BWCVoQ7ET20QYYGkir2pO5sKHhHuadoWl38tM8GLPhWF8vAcDwVCero4bBC9y"
    "7XZci80ykdgS7fVqErzIg9BevTwLGskJXuCZEBN3n6VaSKaLCJvz4MV1R40VGH+PJd0iOcELW7EWH2PhWSyRnuQEL+xEaDMT"
    "NIGglEY0OU2A6biYFWZNFoIYCJZNIyGIhaC5chawJI9NAXhRVwmLJP//1E/Q05DEBN2LSdBmN0PmqpdflpjgBQ0IETtBS6KZ"
    "hkbwgubV8ACCkdwEL2hIP8AMyUTwmELwYp7PpQ8gaP+eXHkIILgOBxmdObQrN8EICCpOkADBHoK3rkpO8EKG9PoAgkd7kj43"
    "EGT0ZDwgqDjBIw0ISk6wJ6lxKGsce6EJGhtE8GLmZIYQPJKc4MXMi5obNAY9IBgoRBDD+mAqi30M2hoQlM0P/U5tD1A3QSTV"
    "wyMgqCXnZiN2K4qlengbCK4U1YxRN0G5wi0Yg7Eu1Vy6oDv2dyQfgxfRF9XvV5rgR90EZbeiFzIeHLBEasi1gGoBQZpP3hk5"
    "ypW0MsGKDiVoydVABiS2V9qvE3SUJngBRyByELs/bsnVxfULVKpmnrVN8bqDlZ1JdIojs6UdbCRBu9XH1IeMQbnd6GQKsB5s"
    "ZsFh2wyxq+kuUtebo0yDgr2ZxeaRtrF1dUUQqxtRNet9dcF9EC3UwVvf69qKINkcgqHwo/vQQs1jtiU8kaY/UphgfYEwMkU7"
    "pCRapmjdanNRkKM/U7hWaHaC5kKOgt7qoiBXf7VBBIklePeLuVADdRD0tFcKB8WNMYgEJ2aOU4L23B6p0TrBYU9TOa1RX+LN"
    "bscW3WWekweLEKSNfuw3+rHSBEWnt/FC+Vcjn+FMt/ZyK14qE6wvEIazEXQWIdgciKsJsllsoj5BTzzBuZOPdgvBFdr3LIX3"
    "MbcQFJfbXsxlt1r4rJxjf6MIpmPk+gwEI2kIBpbC8aBF90VviA3LlpgJzZZZLiZYL/h646pOMBJWWW4stgrXRtCiEFRpgbD+"
    "7JGd/tOZgaC/FEGnRjA0FS73MqkEibBFPHOxqKuN4DoZvCEEyYfJP7/izjDmo6Xe1K0ZhcjaJILZOx7NMe86C71pVDfrxwpv"
    "RTdaCO7P4IsuRrD8xTqV4A+UJ+jPQtBbiqBXe6AThQ+XayEozoosZqsM+he3EHRVJxjuzUEwXOxNaz9+qPD+nxaC0cEcBKPF"
    "3tQpuVah2mdVtxAUlxhdbBGn8qbenSK8CW2lz2RpiSbInVkIOsv11RwRzpMYm0YwmIWguxzBzIJfw/H9wyqfTTY3QX2xnm7Q"
    "ktcHOC/PA4KjCPoLEgxSG5qkgpHCm/CWJRgsSDDKn2blydgKnxffRjCcpR3DJd/UyZ7Gt8mxwluZ2whG84yERd/U3bM3mCCZ"
    "5/tmDCco/kpaFOQj8kDhAyGsmQlai4VdrW/qIXJ/Ewk6h0K+z14seWW3vamLibGJBL0jId+HFgu7UNubPomrLM43j2Cwd1EI"
    "Po0J+spWq5UIvq627RUh34cXC5xbCa5kEm8TCHpzjI7lAmfcSdBV1oqW5vfqoSrh9hwEZwy7OgASqzkGN4Dglvik2qwN1QEw"
    "tImPN4CgXyEYGZtFUO8gGNgkwKrOg61RUqTPkFSbsaE6CaJ8z5bankydoDMHQU8GgmdEYYJG69zwcyIImlISfKVymUXri4VC"
    "eqG5WE2Y0UHwNRAcb7SlIEiULnVqf4dZCAayEvQ3gKA3B8EQCIqb4EUQtIHgjAT9OQhGshIMgKCUBO9fKIIi3gEtVlGUErxH"
    "fdNnG2pFw1kIOrMS/Cx9xsebSVCEgcOLXXdopOl6ZoLKWFFjaYJzRc4moR47Uj4WV82y+y4XbRaC/pwECf11/8JUmKDZQVDA"
    "FLWctUpzCX9IrbX4qrWhY5C/gdPnK++nxzEB3dig5Z5LpCcjwMAZ84x0pki0/Ah4QwkGsxCcyRlFm0qwqwCI/0tYyy3jdBJE"
    "G0qQzGLK/OUJKj0PdhbCztKM/vLv6WwsQWeOL/OXtzWOyhH9vASXWwTQgaCwZpyHYFfcG+kECE5oRgkIGkofKDMnQZMs1tk7"
    "l+ifKk0QzUjQkpSg2rVqNhBUu8piVoI2jEEgyHUK3oya7S6C7hxzbiQnQRfGIKvfOw9Ba3MJWksTJEAQCE40NUAQCF4YgmQ5"
    "gmhzfVHzYhDEQFAcQUfKMegCQbkI2kBQcYKf2FyCM5bd6wsS1IGgsK+aJy96MQlGQBAIMnxVICdBbxMI8p6hliR4byhBRxmC"
    "5nyWZEkrCgTFfVW0uKlRnOCMGwiVIqhtBEFnluG+uKmhal8ZgjQn7UxM25pM/cQW8prW5o5BWqorP3R6Fita/xYsJBKzN3ce"
    "pBJEcxIMalbdl4FguLcRY5DMQjCqmbtQBoKB2lbUn5VgNWixxRTb4otFMLeinCcDpjt/sZgYfyhBdUq2qb7o+u4Qvk4F022V"
    "eK7jwDaaYGgLCektltwPkYOgqzbB9f3swTwEg5pRn2eu2JRgQu8664/vaLBZlrHEENQ3OKDvHINkHoKk9jjO4gSjjSHItS0R"
    "g80yxRA0LixBd0MIXtwxyNUZxQyenynGEdQ3OKDvJhjMQ9CTjaCrOkExPlm7FX2vStBbnKC2OQTdWQg6oglqmzsN9r2bDwQV"
    "J8jTL2QmKCApWZqDX2xSsSgDQVdIK7Z+iSGIYKn3PN4sR6aXoH8RCToqAezz0sI5rKgr3IoOI/jeJhEk845BU1A8XSL4fMPm"
    "wYtHkGyaJ4NnmxNYcjKWIIL2BSb4vcvix4FXbekQCPIkSCLkAUGZhfoJ+vMRRIIIDpsH/c0iSOYcg6IINi1N2G58XjgbRpDM"
    "OAaxIIKfaX5nu2H9ggYER/uiWFBi+XrzO9s3pO1uHMFQfYJXGl/utxKMdjaOIKcWJazzoACCew2CkT3sda+oTJBTVM/y+UjQ"
    "Evle8zVPhhG8rTRBLhOhzkIQCyK403zNB4MIGvLGiCyxLpeJ0FhyDO4MCOmpb2s4ShPkkqg0WbLnSNT6nDWRoKUBQYuFoC2K"
    "oDGR4E0gOISgK+A9JxKU+D5Cay6CNku0Io4g+0To0x0Z3QGCixK0JhG0XLXHIBcTglgIWsJWd9hPdaJ9u+UAwY6kWlgPGtdt"
    "eJXfe+qTCErsyMwXD44heFsWgncUJ8glUcn08Xp1JuKZysJTCAZAsItg2ErwYOb0YVs0qvuKEyRirVj9LAsxVQ6srgytuxoy"
    "E2Tqmhx8aYPNfcfCCOoHeDRB0wWCgwgGC5obqtsmcVa0/bUeci6/M9j6BxJI0BpN8JqCBAPMeYHQZCNo1wgas8+ENILXVSRo"
    "L0iw1Ihc1+WssfPgPhDsJOjVG1kUQZPMlb6QYR60Ob+VxUbQrA8DngSNmbw2OQgecyZojyTIVcZFInh/EwkyBBSRtikE/zHn"
    "10IDCIo7kad/EPobQ/BkPoLvz0ewv9jC2xiCTzknRjtSWv/3jATtjZsGGVP2rkiCZEaC1uaNwbkIMq7nmIIPdDE3zpGRgqA7"
    "H8E+V+aHQLBFOqPlsgQT1DfOiEpB0K97Gu5iBMf1ne0lCfYse/45J4IGYz2qaILaxk2DfQSfcCJoMiaTbdG2bMPS2v0EH81B"
    "sGS7hBPE4wnuKUnwGSeCFqP/IJwgGk9w/0JbUXsQQX8pghs4D5qcCCLGdDISTdC+aPPgMSeCmHFzFOa3WWqMOQ82j+App0CX"
    "1YEQTtDYsLWl3uUWXgRZwzDhBPVNI8i4v1wwQTIfQY0LQYn2MjHuJvCF9vxSQIiFOxQ83tOQ6Dh8xu3lAX+CocIETfUITm1S"
    "o4egOxtBfdPGIOO+yIg/wQjT5lksOrCmE8zPyesiuFP+EFaCrmiAzHuTBRBEtL4vPLA2yIc0G2P0zxZXxhDUNpggsWhjfCGC"
    "vjbMY5Mn+8ZKUIAVrVaFz0jwlLqCjQcR3JaGoLEgwQc0VwaLJ3hMNTFY0Yh+SYKPaU7gDL7ou9TXQxtW7zsHwWe0L0Di40F9"
    "owjiBT0ZH1Nielv4Mh3ROgi6qgFkP+hIAMEAUXIG4gne1KkJC1twmePC0+BkgrSuEvwtihm1uB1g00pQoxZTDiQoS82MuSTB"
    "sGrDK08kcCxsG42kXrjuOgP6gRyyliRIHNSMJ8QT3Em/Iqg5wgO3npqS+Dz1V+Fdy9xN0EXNeIJXXU5X47+ov7anHaZfzO4D"
    "S3J7gdE8OWZOgueUBawZCL6V9Jzya7v5F3cRrN3lcyAFQbt57sicBMkyBDUnPq8qRNWXM/oI1pDJcYtP8hKOVAQz70YowY+S"
    "KsFIYyG4L2GsmDarM8fmJYPZWfqE+Lgsee/QrvYdXcVyUXM+gjq7u4sFx4PZw5QWmH0mgjIG+9nV4VgugnfQLATrTrCuYsFv"
    "Ykc8tryMJ96KOqVBKHb9jTYBK0mQDCDocm20zq+I//8lke+9vSkEs1PJTVkIeqVfvSzyxS9VY1FPWYJZdsmehSDDZJsv8sb3"
    "Vgs9Fll/UrnM3C0IKrZEn23VQ7IQzAdAfOuxWILHlTorpxj6HQRlPKgZU9ZZZSC4KzyciOmtTc9TTVmClNJpYTkZFoJheX4W"
    "bn3s79XO5UOqEiTzEETsY1B7Kno3tJ4QxM0aqw6CEh6DYMhGcJ0QeWcOguZ3cdUFxsp5MvMStAcQtEQnKGOC913crFTtILgv"
    "azAhI0FTNEEjyRmkZuGsnApylSJoy0MQVys5hBM0kxdC1dlXvVI1NCvBroqcfBdTaYiIJfjWO/GXoeaODbUCeiwPwfRRzksE"
    "Bae3PlfU+JaSeVEIBMcRJLXNEuIJmqsv0xvp2OCGWgSJbGNwTXALiycYrH1xvyD4s0oB1IcRdAUS/BPcONhJMEH9ob9ugKAg"
    "qNYQNOQh6JC5CWqWt55Gwm0gqCJBd+3JhJdygmMzMgdKEJw6D3blD+7NT3C7CKeiyQQPLwRBYwBB/emsBLdyv8ADKzry6x7V"
    "x+DxLFOSXUnmjSd4Awg+qRO0ZlkkqBLURhO8DgTN+lkuxiwETU4EwYrmBEuWcxaCRpUgAoJjEwhRkyCeozF1IMgpiRdZixKM"
    "1iGMYgSHLfCKPGh7qTFo1HfcKEbQmpkg6iVYmvuQOyPBDxQlOGyJfrprgXqt6NwE9eqrYfLeRhP0HGEEQwrBWZqgStBS7Tig"
    "YUUW5KUrrMeEzXlwHoLWhSL4SlxAGDR90buzNMEnKuGEpdqhasOKLKa7Mu0BYb57yp+bYDWkNxWrcxpMUNyNE0FzHrwxI8Ho"
    "Wm6UFCM4EOD01YLWLuM3Cc5zWIuelFjdzXa6oRAI8iM4Y1ojONjN5kHFCBpDCU5+PyQhQY28+YO9K2oSNIcSjMQRNBcjqJdM"
    "ixEBwZEEgyUJFhGEEWw4QSKOoLEcweiwiO99IDiSYFgieDhjE2xf0/RSlGsqRtAaTNARRTBaaAzqyClfbAUElSOofaGDoC49"
    "QXswQVcAQVS3orPqYxWbbSg2BtHsBO22lcF8bcKbvREOv9FOcFt2ggPQcboOu53gghF9maCn1hgcQJBTuGa3re2GNhAUTBCL"
    "Iph2jpzgwhG14W4uQcSlgWkEjyUag4ppyA7eJw+5pLbttilWkjEo5UHanAiecCHYnpOZdwwOjvSuSklwyOLSn59wSav1EpQ1"
    "s3xbyqcakhb9Fw+5JGXaM9tIsnnQrPo0gfIEv8+nhVvX6EPpCFatrpzz45C0aPALXFqY9BGUJh67pimgQQS/zGWeIj1WNJqr"
    "r/edo28QFdJrQxLbocmjUqbd+83Oap+lyCG+utPo/pUdNc6VGUTQ5lFn0U7QQ3xKqZgmY61vEUI/UaN2e8jShMeFYHv84uH5"
    "gonkxt2gx8dzNo0g0TCHgLCD4HzhoBETNKMeD6FC8NJGEORxvbEpA0Ez6CVoV99Tl7WKFI8h6Ioh+Hw2gnp24243wQozM9za"
    "AILfNTgEbBSCLyr/miGgNxKCRqcxQasHKR11J23908CdZxza2GodfB/OF9Cno6/TmODkbnPm4FERgs842Dmr9WPJ3Ek15HcG"
    "PV7Zbu5KCnDgAb8vOYT0VuvQnp2gTe+K+5nLXHuQvU0geMaBoN1H0Jvx7Sk/3LvnpwSj+N+ldPbBBhGMOBOsXpwnPBOyX8wh"
    "lPGOzsOUYH2AelISHLx7cDpBq30D/UwEi8dHAdU7dxNXtP5n7gYRnJSUMZcmuJ8c9XU7tQcOzbdzs2CiKjlzbOb8BHVquWjA"
    "b19Gn27jrx3qDxNAlINHjOwJGgT1jSLo8CUYzUuQOHcMEgZOemEIhWBqTN2qHwoEuww3ItpMBC/rzp2b+l/pJNi7tfrPT0eU"
    "FolSYyrnvMfgVoje/EKfeucieNPw7+yZ34qP3NuPfVKT0iJBk+ChtNvQbAkJijQ5eoT8G9rVD9KjhhpXpVtxi0SZrVdjDEpD"
    "8P4cY/AKeRLFjmh+KH1jjwv+dnxJyeWUYOk5dmSN58fsHpxM0FyMYNxdo06HBL0f37oUZ4WMynNsyRrPDz9UjUPii07QyBco"
    "BFov3Guj7R/8Q5w+gVlJW/wdTZfVppL5CVr0A5ojUzRBvW2WPSwIvkl+5916OLgv7U5eXRaCoRXaoj0Zi/Lpn3CSZEtuMK00"
    "8ftHzZWJHSDY7TyFVoDEEjxIbymv3ayT7fbMR6F1nq292JV33JJ1aWl0WlQAQTvAQgnqwTvUz07Z5e9jpgTPHFwx5ttS3kIv"
    "G8FzsfGg2bmocitvjzS59+olVuVKenMBgqhr04uwaAJ3ElwHe19Kfu31XLX/QHBo1NSGZa9plBQhaC1AEHdsehFGkPV02x2L"
    "SnAPCA4h6Iobg2FfzeDWj1OPMj7atLQof4IuElvplH180Nc9LPpx4p60BJEsBJ0ZCL6PSYB7Shmv0gm60hIcmRadZOg6d0UJ"
    "iiaMxCqifu9EpxKU+ITKBQjq9OI3IpRgSsTuGoCXas55ieAViY83JPMTpCYRQo0IdeNTIp0n+ph1165AeFdegLo0BI0yTSHT"
    "YB/Bt+quXfEcEoeG5gIEzT6CIrZN2P0fm678IhrBO/ISHBtMTAm6za4zFgQS3O+LBJ2aY1BY0dvyEsQLELS6zuMSR7A/RPFq"
    "joGvQDQ4ehqc4i4afSkZ/1AAwRe9dl+nEEx7qsQnxhpLEKQOfE9wQP9j/QXXDYLuqocnPzMcaQmaixCk5YE8a4ntg1W5VYJB"
    "3NcSb8aSdxrUliBInQd9a4ktvJ3zoJf8R/yzyxtIcEqARPV/A6EEt5k2jtUIOomJiv/iNSDYa0QrGwj5Hyezs+80oTZ0VJlX"
    "Ik23ssB3FwgyjEGhBK88b3iTMZVaHf1hheDKEvzY0d6xq0mt0dFEyJtgOZrgTxC9aoCIzyHZ6/Lt0lEr+3WgrASfzUqQf14U"
    "N7OAyNP2/naXm5URlLxizRxLcMowQV3nXoohSKgEP/5jXd3Lyfq4thEET4WXqs1O0F795Ktd2Ybsb0huRVlzMicczyKh52LL"
    "ORnujaa3EPygy7XLrOfdjSToTxwQcxM0KAQtl5qwxnWClzbDilr8bGgbQSyQoEUbg6uX+G6Xl5URNOUOJ1irRW1+ZU4t/q9Q"
    "gohO0P/pLpuUd3JPaoKMC7yRxXEa7CfI3f3DNCvq6/6ljh4d7eUEnQ0YgyHiFgwuQpBmNiyPQhA3X9J85m4AwYAnQbr3VDnc"
    "kHObmXSClHuwKBHvRhL0J7cnpXIKc/OU2Aiu5rf6D3VaGcnuPakJmqMITmtg+tzrEnEE7TaCfod1yAle0aUmyBgPBpifK9qy"
    "U+MRv0FO/UYaQfzNDotUjExnAwiGmNupeEwEOY9BXCW4R7eihxWCxRxpSE1QG0Vwenv25M75Li/pNbtxIyNoVAnervTnEkFt"
    "EwgKDweL85z4p7b12rBGyVKu5dUufAm2iMCARpjGVPyGIgmeCSJYGm7IiwnavpV2xYPsH+W6f1X20Gvjqu6n+RkGA0GxVhQF"
    "bkLQTjtKGFdB3dK0O7YwOy5DYpSfn2HOTtCoE4ySMeilx9wnF7Xqq155wxbnSwnUmEIZR0SfqRCM+PfSjKCezBwrgpdsD4dp"
    "j0odU+0u5vaOEroyqTCPSd5m8GT4ErRLg0p/V/sPUEzQJB5KCYba7m68WHgXFzWrpYlCl50gHkxwopuBxA9z2iv6uc3Rvpz0"
    "wRVBOyOoX0PxECW4qBsv/e1Lm0QQ8UiYzE+QVAi+mx6YZhLXTo/T9uNHclZ/8rZvCNxELExDTiM55jHJk5kJ7ukZwY85CcFj"
    "siYYFm0QezSWry+8cWMWgvbE1u1ynSIRBPf1LJcbz3XXPkGeksyKOgXBJ07s7zx1NcrXH24Swf+UkK+JzMRGSIQVTb/xnrMi"
    "qKNXyX+8l86D66AlvifybgxWtXA+HhJDQnqHw7uZXSsgWABBJyV47JrO2gB48ZDzq4fLHOAo9woClQgOSsq8i6e/W0cKISBY"
    "wCK9k/YZ2zW1MkGDBHZ1Rv+Fu4dpayjlx2i7gwgansgeE/zd3xaRErGTGdZySibcS2FWv+XKzYxg2dCY0hO8NoSgx2GhBbVH"
    "KsG+JmJxIiEY7ZYnYV+jVT/tZv2r/ONt6QneHeLJ/IHA+DO9rkpEUgYlPeJqmWBAJbiT2nilQomBO0BFfqGVNB0SQBAnn3ed"
    "QtBpEKRWlm5ESuaEm4fY9g1mQtAW4Iwmr5gSNEvTbL2b2OSrqclVyIIOIHjKy0NsDejvxwQNEUvk8Suebwd1grg22WLy/eQ3"
    "ip+izSEYYW4EWwP6B+kRSoII+maFoK/lN11nZxxc07SHyX9bCq0MDiGoPeFl2sxOgrqINfKEoPGH5WA0JfgyzqW5exlBkhF0"
    "N5EgcZKm/TNNIMEn1THIMZxIOoRxUCboJgTfxASdoiVWBD0jUgygxpxPW+lbIgmeZqdgcXZGzXRc+/pBfR5MdqQlA/CqkxKM"
    "R6bubyhBP7506lAkwdRyvsN7IryUEax+e5ASzAb6zawlEsu9r22kFSWhyalRrW6CFm+Cl1PfiUIQn59G2+s4MAYdaiqKkWBk"
    "c3pBu7sO1eK9QniVSjB+FRRaZPto7SP/kw0nSCxOuQrESlDjRdAsZcrN0iyLApP8o8p0oiZB1oSaOTdBTmPwSvqRKUE9//ho"
    "9S72imDxSrs4sa2Hm0vwPifvEHXPgybvktuU4HmWELIrBI3Sl1zFSTzqqMCsupnKZibIJ8YuWe1XFIIG/6Lp8nIDKn265epG"
    "6ZCDhKChxKirrtKyEnzEyazhlhrfBsHv8ySYvfL2w1JF78cczQhrBLeUIKiPIuj+Fp9vL33f406Cf83rfe1iUn1r/ek/TLfm"
    "pmfYb6fRhDrVMRVjz7SR/sGqF+/zGxFFHq1SJBN7Mib/tBoquUUVgsWMkvyTKJeN6Y+wKwR5Zbk6turHBLmn1dIt2DvpBFIm"
    "WMx56Um/2FUG2uFQgsEX5iCIkmGHua8v4WIetMtbawqCHy/l1lTQ7uAxGH6aX/FIK8HQToYd94CwvAXbKttoQ1NV+g5Ti1YI"
    "hje4ecI9BE3e5zqVt3/adILx7iRTJYJsLVpu3AN+gW4PQcPiHRCmBLebY1CvEPx3FSK41TQyvUv0/HIVRnctnPEh71OBjDYr"
    "WhDcVsyKbg1Pqzk72iwEXfoVqtMn3mCjCI5IjLocL1DsXiDkT9BqJehcIII+p5ujjrTu1Pa5+zb3U4Hi73vcIBhpimSxOREM"
    "5vq+l4j7aQhJD/QKmgXB2EH99y4IwfCQnyfc+UXP+Z+LVX7+CsHkoPskzrh8dfMJ7nP7ui32kxccbj2mtF++1D2+GN19mni8"
    "VrDxBHnvQ2FcDuGRQdTLs0CVIM7/yHI3niBZhKDHjWBeQogrA/wT+fC01PZp0MwE5zqAL5UbE4xuN9/124mBfe4mBlbtMWjO"
    "NiUNJchhdtK9OIMQ/loW8pUIvki2m6b3s+55ShNkMmveHF/3kP/sa7gxwfMd7d06wVM/PpYytaB7ansyTGbUm2MMWvxtt5GY"
    "mHPaq65e6Y6WrtJfuaE2QXtWgu3xYHwz0AvOtttMCJ7RCLppiiiulLmmOEFrJqeiN6K3SPhZzuHE5YRgkJ9PaDcHeJyZuXZT"
    "bYLmvGm1rrLwwOA+8tNawysNglEpV2vtwhjk4sk4JDC595v0Rvmbh9l/GI28eUxQ8cQokoWgi6vXhnBZnTCTj7mbGmTzWxrt"
    "jS4rTvDjMyW4ejuMh8g592SeFTsyeuYUma5Os9CqE2SoswhnGfI+EpBIWE19n3HM/G75Yhou98ltIMgneAmQgCBm9Zm/5ZRO"
    "tRVgVVQgeD7LGIyQABd49bG3HEQa0/DhBhE0Zg0muhwnxH/sr14u8DQc1b++OsVe2XiC/jwEH/JfEzHTc4aixhi8Vf4ttdfo"
    "WawoT4IdSbyn/H1g5K8m0/JZaSe0VwKCXAme8XRlsLf6DKtE0KJ9suI5GW3OxDZDIv2MZ9fB/yuJj14OG1+/Sb4owyCcleBL"
    "bi6U7mj4z0l+3lb16x0gOAvBac7o1gregyh+P69hRbWN0pxJtX6Cz3jm1fBxQtBtvCwQnJKo7NZjjuGEHncCo/ICJvcsExBs"
    "btrn9s1GzKpKMI0IN4xgb62TMyfBY44zsBk7QzWCNu/4CAh2FTz5kwl6VILBZhFE8xG81OvJRDZHglb87LVD/awNtKL2fAS3"
    "BhIMJr9ZgszVaq7MhllRaz6Ceq/JDm2OqxNJNsauEjSyovtNkjkjQWcYwYkBIc7ukXHqBN0LRnBOt6lKkEz9Mk9L70mupaDO"
    "Nyqr1r9COKfbVCPoTOyabtJn0k/ZL/pQpAHBmcbgJHOXuKLFJWdHRR/aMIJ9ngzP1700cAxOCunTg77qIzl+gnCzrGhfo36P"
    "53fhQdHENLcfUS8atC9eRO/N+F11gpOaOjmyVK/bYmvz1ibsmRLbl5gIIn7laukZhjSC0dWLQjBpz5EEG41kB8MJTpmD9WQI"
    "08cgvigEE7/icKQNo01LeEaCxvracrfhekcXhqA1+mWNxtjF1QV4trrfaeEgjWDSi8ILY0Wt0S9rNbwQQmrbywQfo2G3ENw8"
    "Z7TLkzFHvyzKBu9emeDpzATd1GhWP2TnQhG0RgcTede/UUlIDtYERzhNiDYJxi98cQiObkMjC8eLi22XIJjOhqSZhIpuXSCC"
    "4+yYmTU/Xo9hYxTBCekETL7TSnCznFFbRF7bWu/LDScRnJBWw3lXimjPpuJdg+MIRqNNWK0LjCM4YcK6mxMMKc/26uLkRb2x"
    "Jqz+CbMTvJMPuJDSZb2LQ3B0TrJuCK1RBCeE3gf51/rNdNtm1Vl0WtHvjs5J1u3wOIKTPQ5KPBSfLOpsEsGOpsVjrY3R9Gbt"
    "xQi6TQPxzfz/Xtpogq8CjEf2VbMZkIwjSDi8HWWSPtoognaHJ7/PpVc4/dOtsFJHKsFiZH9u0wny8Y7cmnfarVHVatfaCUaU"
    "p1tb+xebMCEiIfmQxgcxj7qTMWk15Lb2z6CDoLUR+7Fbx+D4rIXedEfY06KnYwjioPXtfMrPmiw3kuD4jzRry+7+kID+ySiC"
    "YauF8SiW1bkIBM8ifgRXINgdmcdjCLb2N0Sxk2ZE8Wk2kGDI6SODgV7o8zGTcavLgyl/YKQm90o8dLc3mOCElGSFmTcuG8OJ"
    "IHVwpgm3nXj63ASCLUMkHO+KVr0WZxJBn5Vgi7mlZnX2CgdoEwhi7jnlKsGv2OIJ6m0EDerYXBPcjKI1/qsCRleILmR5qUkw"
    "yyYZ3a4KCXc2l+AEL83qOJ5iLoJZMGt0dMTd2Be11Aeo8ydocxyD4UQr2k0QEVt9ggZ/gpgjwWgaQfoVrek8uB33NVvxtJrf"
    "vrgUcusTSxI0OzyhhOCJ2gR1IQSt5uaLCZpG8O0OgpcaB10oSDBqT4uOD+g/V/2gr04j6DAOe/rvoQ6CRuOgi80i6PMag569"
    "IEHckZcwdh2sOsFPhe3Lg+NTMu/UBvM0gi4jwZZQqYvgVx4rvyH7S3772rk7+lNx5/EUgghGLfOj1zV5PlG+/D42lTjEnAtU"
    "ah/0bAaC+jiC6m+gSE6tohMc/2b1FMG9aQQ9tu8MW8Zm119HL1W3onoHwZAbQf1kEsF+j2qrnaDVOYSNECk+Bs2Y4M8EmK8r"
    "WidoTCPYH9VYThtBvY+grTbBg+TQI8vHfKdBs346hWiCtrciGLQQdDaZIEpmO8vDfMucakm1CKNJBPvNOYrvN/NbzEGntQiv"
    "Kk1wFyegsEtrtgmX09as6A8nEuxv4rjSkO6xtLmo+cL8dU3pHfU7MUFHJ7SYfsrStVn7JPxwDoJ+J8HDhu9TiqeU1Ufi0kzX"
    "ILS82hTbUkuqiSdI+sfgfu3n69lR6TILc/V6xDVD2upEwG0Mkj8nE9VvtWOCdJ8zJ3i99vP1b5+qPA/Gfhr27ZC2xhvxI/ha"
    "NEEjIeh0Erxd+/mtwplRnOC1KyjICD4SZEUnE3R6Ca4o4G6Cd+qB1Pr/BUoTXL29lVw1nOQfeXkyvAm6/WN+FVG0TJG/l/77"
    "bu3n6fXXhuIEk10fNnEygpWrIKYQtAlfMRD0WglmcUN9iKZbd00tqTNRVjgmiCItWw5yECcrypug1z/mg+L4thrB/F1roAwn"
    "I6h76gJMPe2kVCs9pgpxGoOIM0GfheD1ll5aChmb4cQ1tQmWLvk2GwS9SWN7AYIHLb0pf6aQFk7cLEeGKk6DfjtBd8IHk5kJ"
    "2jHBI/qf3Vz3qhqpo9S/cXSFc2qlza1WYjdLBH+kKTQG7fjh3YEEE0WfVNmP2UXFQGsQnHT6Zst2RLEEtW6CNpXg3U8Gmro7"
    "X/xSt0ytKOZzkNLWAgRbH/jauo/SBum1g9sKe6JeKV2VEswbDE8j2FLf+1IkQdJH0K4TTOJEc0/ho3715yVOSSZTy8cfXjkG"
    "AXeCr4QRRAwEGwfEmet/qCrjw9LkkRC8l7eX2R5eTXBkxhMMJhC8ubbsNYJG8t5f1dQNJoxyy5ilQ0AmE2zh8GwwuZcDCH6t"
    "m6DRjHBjdOZXtK8rnJGhEQzt+E0tbwJBnRtB12bLD+GO30Gl1GkzIDQfaAqnZMrzi5Ef4xIk55PZIggO92TyhcZoAkFcODs1"
    "VnESx3y8KQSTVn9RGCziXJ9invkQXIGLMAtB2jjdqYzBXYpDtL/6JWNjCGo5Qb/eAvzG4JgqwyNrMkFnPUs0h6l1/5nmKgtQ"
    "r5gVlM2DPpcP5qNAY7xprmuutNzCLjT/8LnKBKuHIN3A6Ro9B4Im13QoA0F9HMGVFTU9TVeYoF/JFKL09EEOBA1eBBMT8SUu"
    "BJ/QV8xMX/uowlbUwTWCjsXlHo0TrgQ709bMBE/pcWVcaKkuwa1q6cj1uOyJx55ybkMwM/KXzD6CRidBr0gyNMayGWnW7ypL"
    "cLtWYWmS8uHFEjgy68cTSlBTt+B3V68SNFb0Lu9JRPBkDSFicJ3aMm+WX3qmusU0f1AsIKqnK/Wbjklyzth02ZyHYHJiiiCC"
    "jtZW46aAbps1twVzIji5Uu1NavIO65mxNlldBJNDuYyW8i1zFfmrS9C3ai+06q083mZ6OJil346KPjGFYNBBMF7lvapsMOHX"
    "K0eMcMqSUhEoT65zcusrEjcYzHabJ2OHpV5VJxhP+3dUJWj4qDYtGBEXgtcRJ4LMTiLq9EVDragaaEa7uhaqSxDXCOqEB0EO"
    "OTV34FEMmJmgX0+raVvqbj4zf6LeJXXMpWfwI8iaLaGO2LyQ145K7nEzZ3jJVJbgJbthVLhERh+ffwx22tyYoP6w1Yr+PUvZ"
    "zWdX7UYnvyJFLEHIOY3gYV8KoYtgy2aQ1QvfspQt2r6BxFwmzLHivoIp7CNYH7FOQdDIY8wawas7h5q6BDERQ/BtMQQ7bo0w"
    "egmaeR1ejZa6wXzecT0BH2xxAxjRHJN2gm47wdWE8YBG8GbxawoGE6II8rOigcFm4MxOgla6qY5K8I7KuwfNZQmGDL/m2WfO"
    "BIKFJ7MiGCLaEq/SVy59ZNr5k5MJ2iwE2SbqHoLJmWNZj2kSVPfiM31hggzTpYvYjITVSRAlBIM2glc2meCOQIIRA8FVy4cD"
    "CNZpH1YI0jZgxBGKstsHrfuixuDn2NwUm8EVZdzG2EMwmQdf0gjGV7leV3YECiP4S/yCCcx2Sm03QVw+4KH6wqa/p+wYNMn/"
    "IIrgDleCLBOh3TkPYtJKcFvbO1Q1I4PZ9saOEbfznILkKf2pBAn5y47NwPc8NQEaRAGCftrPphPs2M6tm96Rmn4Mh1Ng24Q4"
    "E3SnEdS7CF41to/2lSSIGAhuLT0G3ZSgN43gW10Eb1i7B0oS1IlAgtzyotlHBaz90elK2NAJYv3GocqzIBFyRjhHgqlLui+M"
    "oE4eqZkZtYQS5BdM6Iwla5idoFcj6KhZYoH4nL0lmGC4NvbCCGrEcZUkiEUS5LgFW2cseOokaHURxJqaIooRdNneZwRBpGpO"
    "lIngSF/U4BcOCiBY/agdRQmabAS3J3/61L1njJkj/cIRtIhIX9Ti5oquCUZTCNodBK8oStBmPzNwwTEYlgyyy2S3WVJEVcr/"
    "vqIbsJHQMWhwM6LFR4VMfWY4QawoQSyE4B5fXzSuUjOppb8DCaINJEiEjkFeBCsG2WeZeUeMQTVzanrrxC5TTuZldUodTxC1"
    "1vE3r4FRRMnscto/BPenG+kJ+kHVrfUYPDOnn2DNaip6A2/pPGaJCfpVgj4fgrUXJgqvTDwSltjmtEbvVglGDF/o9j9OsBEE"
    "ky778lzU4hKnNfoawa4ZewDB2lBW8Cb6O/krRV//0hYm39gIgrhzrtwsgvHJafmm833NtjR5CTq19I7TT9A/bKR292sEPdUJ"
    "xlcP6espXdCuHT4ENXaC7eN0+6DmWLm1uCpSbgiS/Ob5/kcffCvf3kIE9faQo0Gw+inGMVGMoFm6JFI1gu4IgvrW9W6CppCU"
    "hmAv9DFj7YlsVpSFYKMg+xtBlWDN994yiVq7JnQiOJ9WTXJNPwTBIixJGaN1rUz/51GVYNB4VLWSMgYhbGkqGQn6LK9Veyn9"
    "NHJ7CKoV0puEsKWpZCQYshCsEzolH1QIeooTRCoTbHdGjfbcGyF/ZXZNHZZa4YRF5iFoiiHojyL4+2ZXL1CMICIdOV7ZCIZN"
    "r5aBYNjI1pyaXR9hEaUCQjwTQYMbQURYfC+ziyCxSMcCh6kUQYOIJLgnnmBwZQzBB5tD0CYqjcGgaTXa5qyOAmZUHYOB2gTJ"
    "XAR1bgRpeZruebdJEHU5Q0oRNC4EQbeToNf8qwrFg+ZsBLkUq/nsBDsyNyt8uCuTqBRBWz2C+nCCYVcA1UwKmCrlRZFaBD2a"
    "S8SQqRhGUKnMNlGLoEtLzzn9BJ0ugprKY1DvJpiFc7tSEbRpP+yZH9yOJIbaBA1qyLzm+6P0jMbL0hB0KIa/JSC8IASLVqAR"
    "NDInzk7fO1ieIKX927LbdnvqDfd0AIUIlk6QsSmvk18liZJpZOqOHl5JtZYosdNHCzoIhhTLpAzB4lUC2jE78S3Y2q7ppodz"
    "TN1VJyocbCFot48z3DOCDfK+erOgr32p+Tooyvryf+Npjgxj0KfndsL+OMlpJxjbGavy50a0pQhBs9I2Sb6+UuB8KWl4Fz15"
    "6b3ldVxRNRtBjw/B4sen2YeiiqtjKDgNxm94M26boOGa+5r5hMviPadgYhxBjx5CPUg/VK8Z4gMFU2rxi2lUgryugdE5BRMm"
    "I0HMQvA46xaK7vksEXTyURK2EXQlIBhqdIJR/xj06U/yMH13nRA1CaJqUBu/Wdgca9t2zxaTxQlSH669/sdoxJjKEqynJVqs"
    "ZdwWP9JkIWi1RRld0UTF0Jo0gs4SAPa4BRNRgcqnzigcqu84VFkEbQRpNt5uNbRfkIbgLW7BRFj4pp7sBG3CZkZRK8Ffb/zd"
    "pQhOvWsU1WcJs5UghzVrc2aC7elrk0bQXYIgmtZv9MY80k6Qg7NtLUvQ6SKoLUQQe7zMWomgTx2rgRRj0G9ax3aClHROpnea"
    "cygSuGmri6DLmaBB9wn4LN0byxL0W62BmwxsX0GCJiNBI3rII1riRRC3rRt2EwzavNTkjRfatTvRf2oeT2ZQ50Hk24FEBMk4"
    "gqSToLFMfeHEM/Xt5iRBnQctZ2dfHoI6YbOienvIiCgz5DKJ0Zu8gon129VnvPc1fqcDcSJokHHzYGmQ0QgaX1+C4MSrYnGz"
    "AeoEMXm4LxFBr9WldfsJkrbRmaLdX4Lg/lSCUf0g4zpBRPglKziNQZs7QUWPZE4I5pe/R20EY8KHchFEowk6LQ+iLkGy3kUX"
    "ln4U1giGcllRvd2+dudkCsqfpaG9rCJB1IyV6j3S4FiGb3Ih2NIPnjn9BHPKp9SVfxUJWs18RbNglF+kyyer1vIpL9kJbj2l"
    "EbSXILAjhGDFc7HItwV0mCljsOVTzhgIZtZEf0ozr9cWGUMT/77dnEVqToHxlGPKXijB+nPutBP8KHUSvbkEQX7Lg16537oV"
    "xvwIYi4EbTaCqJ2gRSV4XVNQdvP1cdWtQzxPyuNDEBEmZ3T1Sm3FNBaV/m21PRm3PCy9crwR7sclv7IQdNs/pX6Ztd/8zVaC"
    "7zvLjMEdfgSdsr/olwn+lSbZGOxcvi/5vWHrGLSpWdUbao9Bpxzle+X0Pt8EwmwEV6+mtxHEVII3N4WgXiXIMeHE40gnt51g"
    "VH+1ewMIrl758uHs7X+FY4hdduJKm5d08l1+z8tp20Tnloqyk/aobZjSB/Dl7ytI0KL1X6P06QbPAq5ZCa48MrdtmGJaLfhl"
    "pOJVS6gjOX81BviCZxnsFIJhYSs6N6aVvSYXtfwKzaNyr2IVdy/9QgfB64kp4tkvpxCM8DCC8Xc9pg21w5ZP8O8SxS4oSPRb"
    "HdvvDpJX9SUhmJ9j1/UpXs1rekTzdpwWgi/jP/0Hs7Y+jzN6cCvB7awZuHbLKQQf9hP0az6aS/md/W8cdjzH92YleJVnkzYI"
    "Gpmj48pC8GQYQYtuRclV8s0uW+CqNgbbCZpZP+b6yHgywbCLYFDL+HqU3/mv13e8UfWBavNgO0Hrh7EjyrkI1p5A8EkOiY3g"
    "p+IxSZ1Ov73HQlBXjWDznOkoNkQR3wq8KeuDz9aGsj3iYBrv7rc7CP5gTdBRnWB8Jyj3gyqnEPTX7ibTGGz/Lu/rWx1By/r9"
    "1SCotxPUV6E89wBpSp1McJp5GjqbG9KahH359Y7HiPLbTy3lCWrY07lfgzaFoG9mQ0Rny6q1/trLn+54jPBatmJnu0oQNDoI"
    "WgKc60m1aj+ZzXTtBNlCl+hShzEP0bvpzG97ShA0233RtKGE9ZgROss6msFE0HBaCVpPu5J33/uHihDcqc72lKjhx/nHt5PS"
    "agHq2rlUz+3afpszGnWmXwl5mLw1kj5HuluNz2hxH9nXZCIYZgRNtmAiGpU+iPIZBUm/TmFXY6Z5lsbEEgw4JfDSi53kJ+gs"
    "QHBSYjSys5NcWQhOWopUZAxWV1lmIjipWC0jaLMkto2pY1D+Bfv4KCFdKYKxJ+N2EfQ4EXyjCEGt85JTUd86xbjZPQRdXpFn"
    "8qTSbwqNtM4rMmUkiPKzlxgcmUmRp6MCQSOs+gQzEZyyvEQygpilWnSS15vs1ZedoLlxBKsR+FUy0RmVnqAVVNuzlaAhzfJS"
    "TrDR3lZz59JPfX4qQUv2M5vt2pkQM0U/U7dhe5QZLjB/YFEKtie6MqbsBG8eVe1R6xjke/PJ1J0TLmUYB+nHcvOY0o4iPcHg"
    "sDrbzzQPTq27Xw20t+s/ey/tixrHMeilNQpSu6L1ZZq5ckhkqnnTqb4/rrmiPAg6cruiPivBK3y/eFJaLcZEJ4hqRsSebKx1"
    "yQla9SR/K8E7EoUT7QTt2gtMH4PaMqdus+dG6seTtc6DnLcmTzuPJKT5QilBnyfBl9rk05OFZ5iDmkULZ7Kikwk24pEXbvKx"
    "XAnG4w/JTZAwE9yTiWBAIfjE0xpnZOt48wn6m0VQr6Zkpg7BmKDc5YZ6o/Z5rtWwaQRpx+I9SM9O9/h9S/pFlic3Qbfm1alL"
    "8Di9vyBt7+19bgQl3/oSEzR7CequZAQ9GsGEHUoJ2mfcCGryE7T7CfJ/EXMqQYtOMC3Qjc2Ke21v+jwo/6nNcRCFOyrWS5kb"
    "mQi6TSclMt01QetV9mvoAhDUtC3cWia0zp7yJ2hMdvLrIaKREDTL607BZILyX+gaNUYDjaAVSEbQaRIMjOTJVxxLm0AmA5Q8"
    "KbqaL8LGhEK9xlY2gpTUeEZQc7XpA6+nQ8tG0GYgyD/G0CcSbPz9nOCRSS4aQdT/yFhAlDjVv2j4/VnIc4svQdnDCaM5Bj3a"
    "eJGMYEgj+EvplHVkXagxaDbnQY82Z0XSETTaBsv+xRqDZrMt3JkITlk1oCW2Q265UKUIomZbzEUQiSJoXyiC8QKv1RsACSFo"
    "TmtWq7Wp7Qs1D9brLiM8G0EdCHIJq53qG7cRvCtgjWVas9p0gsEFI2iS9zS9UudEJWhFd0VY8EnNiugEo4tFUP/vSc0VDanz"
    "oBWIuIEBTWpWTEl2x+P6ucOX4Eu5Cb6OagQDdQlmc6vHNy0qeWrbIvWliTP6XeDhDbkIus1ZNMrS5SFvgq7MBG1a3SWNYHRd"
    "yLdPaFWdEiKmH8njTidlCCbvjfsXpcXEtfYUy0YnyBme/CF98t79ZQW6mB1NE7JflLSop/G5SoZQu4asjkzcwfT+mVsX0xEn"
    "ETRnIyjzcTJG/N56v92XjmBE+cvZC10sguYD2oQyG0GTO0HzohHcM2nVCi5tvvTEmIDxjWrTpm900QiumoFCkJr/4u5SX5ky"
    "a4XbTViiXFG5K0YtmksQ0MYgd4JxiuAnRxO83IAVcV+UUIYg7k/lmgJSS1emrE4EqPHYoSgjSkKZQ3or0jSGCFYAwaNJeTUf"
    "f4w2WwkxonInZVYEdYaZWwDB1UDfH+87etim2X7hBLdlJGgw2H2T/+6BvcSOjvVGXWLNSPB9mcdgQBkG0RHF7ef9zTvJ/8Z6"
    "o/cJtcZCDECpXRnLp/lvzgwEU4hj29wkDygE9QtI0GYlyPkltnOCeCzBY4oHLYqgzCE99mnu4D3hY3B72gJTZGa3SFbdjeEE"
    "H7Lm0eUlqO0ghhUxQ9hLjHNGQ14EP9rz56+kJ0i0HRazYQibCsYZvtBqEnTGeLb3ev78uezzoEG0j7BM3aaYqcAZ68rwIhg9"
    "7vmFP5aeYNQyCBoE7wiz46MI2s3ryZ0RJjnqW6HUZPdkzOjAaC+wu75/kP0eim6LeoRRebUQZfat2uls3p5MpMs+Bu3w0GjP"
    "I91dR/Y4ElYrMsoZDXCDYCBiaSJK+9e5vARRPSXzrEywyAeSSFi91qhKCx/nXqJYggTJbkVXYXC1BR+VrSj5ytphlIygR8ib"
    "WRaXZCdorEZZtQX/eZ53dLQ7RQhhCNz+MSogfEafuvkntu226j1ZsqKkzfI89vXQygjuCSVo8CK4zzux/Wo9BuVdIIzXd1ss"
    "z8v46VPrYcfjRNg7jArpX1IDIM5p0ZfP1wQ9WQnGx/y0WJ6zomDGdi3ZCL6iJiE4F4u+fEYiQ/KsWgfBUhiEfCTSjvBy/K9y"
    "L/f1P58RlDcetINOgpkLhs+JAgRX7sZ9zgQDO406hey84xYOdhLUnXXea1GCbEdMmi94x/NmSvD9HakJdr3BA3fliNrLE/SY"
    "gkb+FfcmxY85lGt1MOhpwOh/+c1/zRYcEbHYR6YZ7gF3ghaRPByMLwvpcQVDLDymZVkiZ3JYnzJyOW/kPdv0oQoEe3p3hEW/"
    "BAOckAXzkyEpudI6Y5eOieThoBQEGQxkwJAv862BBE/ijwy7v/20lDWXlKDPnJZckqBbIUj/C95TZoKJyxpeQ4m3rXatmrEy"
    "DwoQjCqrDpHWjmVQrJd85BuW3z2WNi9qrgga8hOs3I+YZnKvG+yOS1udxglzWKgDwWkEtTJBL1lNiZdVjieGCqfMBCv38O7I"
    "RpDVirqLEdQqBJ3Ye00uLT+ZjaBZJrgr1/Kgx7wouhjBoEIw8SmOk2PST2ci+DqySplt/WtSJbZXBMnSBHWGWbDwRdO/Ez8M"
    "nkAwZC/HCPFzclyOJqQiiGQg2PcEXumXvINSRnACQR8zZ3EC6zl5Wi4SOnakIuh/iTkMXoqgWyZYfvgJBAP2TKpv1773gSsV"
    "wWdkeYKYnWC58eyp82BvRobkAWOUXSeaGP1TuQiyx8G+wKdgCGMoBCcDPA0YQ6modAGqXLHhkOI8calBm5ng86ojPXzFFtWc"
    "0WM2j9TFjqQEB1mcZQniRr3RGIJ4XEzhlaMJqRYqBr29wKiUgSBqpIXGEBwbFZYNkEwEh9X5LUvQbjyBkFMMGQhiiQgaKhCM"
    "1r8USkFwB/mKEowOlyHornlFyxEsDbu3ZCI4rA2cRQhGhcWPWvvfc9EEy+9uK0swWsQUhKX8UetfeyQU38qDrbjOgaoEOU+E"
    "l1gcqpCUfqtmBIwXcxG0qwQlKrmwiByuTIf1Ki3Gfb/uSRcEH4sEeBaiSudBkeYoSlCYF41HdRp9TKHhqHUMVH6OHawuQWEz"
    "OBqXyRux2j5G/0KrEQxNafJq9rBXj2Yn6DAO3aciCbqXUfnNr5PQ8OQheCwFQXPcF2IOY5BpiReXH+TzxDOkiScQsaQgaEwl"
    "OL5qzWWqc8q8T91Pur1EBPv2fczmjLa4Mt9jNb4Px4fqDL9jrYPS24nB8M1QktO2depqi0RZGXfk9DlA32JoAbuakSVXzOiq"
    "HDWHQwL60J6/4LDPao9bpH9eSxn0C1V94jtx19duykBw0CSI5i92ClkJRkNYPu5dMeyJo2KCxEEyEBxiQkMstNACjanrGEfw"
    "ZExQX/7aveQKIyyFIzOU4MxLhD7rLDCIIJ5KcCV35cNKkJcZtEJ/LjYrY04jyMOnYc8n3nM17MhQ74Sn90VJCIZ4ToLxaYLY"
    "lYHgiISUsHUVYxpBMjfBGzLUO+kj0hnRrBY9YMUunGDN7Xqe5LcliQYlycroo/rLLCUyrxtdySY/1KrrFQtltVlds1P2LAln"
    "v1gKgs9LRvRnc8d5X4KVevaxZ8/hyuARWbXZCK6f40puMDwJqmWYCbp4MYIdzkKyRMeVVJsx+rBkC+y854QmCoxwRw2CXuW/"
    "3pvzcTr6S7IvmifAH9gM/pvtFN0t+PFoVxErOks4MTStZvE+k9m1Gfy3rOA+ftjzEEWXgWDtcR70EoyKSMLjS/A5YiGYXo4a"
    "5wDDEJN3FSQoLBsYX6Pkan39xSDrYwiQN5MnU35pnHaqOBCLl1bf1ZdMjo41NqIIRpRuFTb9HWcJgm7RaG/8LHqNs+mR7itH"
    "UFhSxgopSxR1gtajUgfaX4AgTr0rPQ+yvu4pRzC8JIqgz0JwiXiwHNXgbG7+IiH/bUzQv7UcwLHn+h+LyvF5lCWKUMw7VL+D"
    "wSHwS4mszLsiyTgMFiQ4dvNdJGjuTsug9UGLE1x80YBhZSoouX954WESFAa3lyNojyV4KOZ53krnmp8a4jbpc1nRqIhCC7uA"
    "xRZgshOM5CBIza7JQpCUCEaVJ13wLhjEurZWKymdNUzts9izEXSKuSesfPmCCxQ5l+/9xLCM76wEqb+xtSBBuzQn4oUJrh3l"
    "Tw0juC/KN3bWdqqHoCFobaJLX6UQRCxlBOK0nkKiLzCVGQpPjFouZW6jP7qjHcWknRnnwa8V1BJmO7knsRxBo2Wa6yUoyoza"
    "HsWMtsyD5lncfu6MBMMawbW1WI6gyVwAG82TVlsf8WH3+6LxylJysgWei2BUPFxYacIQCBaZ7XzAGagvoo8tKI4bD1FX1CdE"
    "933hBCoxM5YlyJ6QCuepVkNF8tFa1wW0EzTivnRESUtMMa2RNoSgvixB9vc8n4cgXhHMyk62raw2J7xejR7yBdUT4sSTkO7Z"
    "1AymPX6268uM4jKzx4tG9OwEz6r/+U2B8WmYhSpGoBlvgpWdTOpQ7q5/51vrZ3di+/mEkpR2phAMtD5X5tNlgo8WJWiUZ4yz"
    "rtd6M9MKb9Vq6s6RhtO9zmuCnwzrCUFMTUFbYwn6HXPLo7zzFAQTQ7FkWrQ4EcnH7AQFLU3oT5u+OUr/c91Ivx4kJnXP6lnI"
    "G00w7FiwOUvz75VntMiCV0tW7E80YKFtTwS+E8+kVDZZSSbEXBuqbIiaHQ6XO2XhjAQt9jfS88FmVp5RJ2S5HUzVR/x/Fq5V"
    "I28sWm1a0r+Ls1xwF8F0mW/S0mfrHpLEw3EaBOOQRhaCA47ndMQQbA029dKCnNexspmMn2gawU4PJ7ebxVx9EFuyxQhWD0F6"
    "xf42QjLbuD1UMcsEnXaCyc0swcBYl7AdxxJoKCuwt6o7AezlCOrVZnjJ/sZHhyIJOhSXq7Ciz6u/XCWIRhF02QhaHhWZJQ3B"
    "8wGvvC+SYESJW4tjmqOORcGEoD+YoE8GEbSkIVgzRQMqLfb2ZiVoFqbVyP4U9xHU+c+DeW22XTUT5oLRBB4+G6Q62BH6NB0E"
    "VzOi3k7wUVHXyZ1gWO74tbzIUgQv4ZFjMDwSQZB0EDzJG8kknsFEUBNFcNvGNSuBFyN4GY19G/eqUIL1BtGvafYTJ+vw7p+1"
    "83kmkOAf5v0eVQNiXUOLEbyGR3fHa0KtKK1BvpD98E6SIm2J9h6VkracAXrlRFZQcyeWIjghfX9TKEGaa2ckP9xeRdCxCXuH"
    "/mDPxRF0ZSQ42og+8tDsBPV8EMS7Y3Y+27G27gghWGk1v0ZwqWhidIHJ4+cPhXYo6qp82u8/+jf4kaPtaLS1dTQLQbvxgBZZ"
    "agPh6Ld5IeJUxm1cXeCjE1y134MVogfNGroo75FCCEaV1SSvRnChMgtdLoJ6TyFVTjC8WvJkyouaGpmFoN4gaC5FcMLGu0dT"
    "VqV1+o9/rmft40pm+b390rN7JYIOno2gU2vIhcosrAkEBTzyZ3rG4NVsOcU5LA3YckYztETPgztZs0V167EQQXtYJq1CMBRK"
    "MNS2Syuo+eNm3e7bTongS0p5hDiCRpbiCxv2f7kxGMpDEFFrAIwiDvPSh47nQ93sKM8SQ9ApJWmDBkFnsTE4lmAg5nGavmhx"
    "PVWyOK9nx0iY9AosIi6ivxd/5i16Inup5aUpVjS4PhfBP6kQNLJYzOrPf3Em+Dw2DNfpI44sdNQvGv863kv+g9AktIjeJBWC"
    "FkM1qC8msx17K7t0glg9gsGnI9EErQZBJx2oUV8kFIghGB/CF6Vf7UpC0B7/MuHP8Cdo1Ag6NYIke+YYkGH0L+QJIKjF7PSm"
    "zVSQIHnB3/syqqMIuVWCepDZDb8vGREJIuik5camPGNwghUlr/h7X0Z1FF3Lf5r/sZ9h6SVIhBFMAj8szxhEbe74sPUyAXnR"
    "MFkJrBEMsuUUr5egI4agG3/9/3efsnayFEE8sMx3PoKpHTxMnc6C4KUEi9ublHfFEPTiief1KaHlZJYhmE1ouR4uTFCjLcat"
    "Zp1swjVDzSyyyksQjIogxpMiotdrBO3BPVIcQacZD+JwFWAY+Z+1JCLSxSZPDMHVN5v0JeiFCKZP83r9fAPvIfZFEnQbBOMV"
    "HCtxn50OPzol6Asi6K/n37A+Hy1IsNCJRGPQoxFcxdMxODcG9J8512kQ0+XCQBDBYD3/Ngg6MhAcm6vn61nVB7iVfdGq9698"
    "mZja/bB9efNRaRoVSbD29gutLslMMKARPPWTs3geB41fX+tByQjzJxgWBKsWaKEqi1pM9Xrg63xfZIYhKCWOnHV/cxOCr/w0"
    "WqTFhCel3sWfICm+UxKCUdkQvRz4Ns88gQSj0g/XIy5KfuU8zWw5HesTkaaJOTjWMel+3EI3oOnp3eRr92/opIBmIagXObIg"
    "c0HP3YSg0Z3aFkLQplfyXP3VpQhWng4PnRRE5mmLn95dG1E/H3bP9diiloaga/lWPdARcuThCd0NWOjurNorDq3gjoQSLBro"
    "5trxdNZh4Gl8bs/J+j62kBaLNAlyPRtBQoKD+6wrkmAxz+zkK2FhLZD/s/XfcGsxvkNfAxZHsFRaN39edD2kBtf/cq+zwB3B"
    "CkpHllU1tCm15041OIo0KsGIiCP4XQkIhkzed6UVfiiSYNAYno7WqIYyS8ZAr83QBhGqKsEjGQhuDXPGBIxC3O4o4WxkWdXJ"
    "Ti83Zs0CCyaoyaCqTcRsPa/ydxxxBNdNdJDRqN+KVixR1Am6a+81mIngQkOw6rr0lf4GiOQxdfGzXxbXo9aO0kFGI6plAnMH"
    "Jy3FLTtCRRLHb2a/z0UQvLUgwRfMKytmajbLvkR4SyDB3ETfzoeeQyFYOqakIFikfSm36oaGgHlwoZuzjBrB7t7p5Zas3J9D"
    "gQTzzw6yoXbfqVjRKMcW1QlG3QQbMcWLURVflVjqhisFwbNugnrWqkiYK0O3U4FWOpoc1f/4UhGKoSr6GLbLAscbRbCSFUZy"
    "jMGgn2D0t6s+nkiC+djKxn3aYicdKSFUfSiLVPeHts8PowhWUts3lyGYmJPSxQzd15+5ybR5t9rQfCstMI1gXOhu5FardJRf"
    "2PrXfW3t5LQSdCYsq1E6763ixqiZCb4ZYvfjf8aF1FjUKi/qIlj/laCVoFcQ9FubH031ZCqnOq1axV6AoDWoWDQ5jJg4QcUf"
    "nImgmf+XRRgIusWnvWrtjvZkZ3S/ShAvQ3DQucxxk3hhMiK++1REcruVIM6BWV159Vq3Qp0GZXqWu+TK6N6RTpaxoi+GEnye"
    "bP8gPzwRUa+GqWYqXG+W0LSnLASpn9bwkvgSDKwl6g2tQZP4mqC3+j9/8VC8J5MT3EtSD41FW781xcRAMLmxaaLKxHCElqi7"
    "twY+MMqbziL/138sYgy2uQoGoVwC8qM2ghE9uiQTV0M782oWIUsczDVsMndygtHqef/fvy+A4KU2gutjsFBXkYdV+wMiWo52"
    "o/zdoexj0CnabzUJviOAoNkWcFm5zcJdRR529e+JvxnU2Vq/v0EWuT2rj+AZhWAUt9OxmIjebBuDiFC2nEVtnqw/F0HPWvcy"
    "gyyCMCPY6nU/osSDcYXpeezG2PyzakZbJVVO0OgiaNR6lSGcoG+tH+LS5/h7Bcx9Pmq9x/y0Nm/jbG3GRZEe2fwrDvW8Lz1d"
    "ewppkJWXWFhdBO2aly+eYHC8jj13DSGFQ4wrvJ9te0JEWZ0P9XQ4IBE1o0kzPP7RFS1HYRTTXzNG7yFoiidYGnY6/9iK3Wo9"
    "bkv84RaCXqm9OHeph2mT4MwcZkFW/kXV5/ugJRRx5yJYhrYowTbVFnwdvUxQz1Yz+BKMssW+dLCFNzPDlNnMB13FjnqdoDUL"
    "wajclrIRPKOsDz6ICQbrBgvSeUDnlVDyGwnSKPsuvxngBS0v4yxG0FtoHmQlGLegEWb3YBqJw3GeVUfzTglWV+KzU5H1ToJW"
    "naA9C0FSJuhKRrBqRV8k64N6kB0moaeBfXZfKm8nzK5wyr5yu5OgXW/TmQi6pWlYBYKOr2dtR9LTS5JmtCNxBMn65mm7Y4m1"
    "PGy1/sUlAQRXzpd3JBnBqp546YXByV8KjvSM4BtXE3DliV3xgbMzdVEnwcbMNBNBryA4//LSIIIvvGyVLu3nRmZFk7a1X7ni"
    "CCbL6bEj87kugvpSBP01wdnj+aGZQz/uZgnBV6uh5+Spk4TgS85eWHU3J2luW2oQNBsEZ5oHgzXBBVZ4m+svdifBtGgTJ+VD"
    "8Y3fSdYt/BUBl9ZUCOarg53zYLOGbSaC4XrIx+nRpQmGZcvzgFbeFcZuS3Jukp0tUYSH8QAQSDA5CNylrLlng+2gZk7CymeE"
    "sxFc5MaJRnhaJlg7oyu6nhG0vKD8G9GX4iMJ/AOx614uzeanU0FYS07UCIqcDk/LdVWBDAQrOqkRvJIR3HV/u0IwmRsjvo60"
    "QSFoUNacY9W3FYbVlReRBB+Uwgnky0bQr4+DXc1Krp/d1vLR+aS07vQ3wgmaLaFYkrU5aboWMxDUS+FEep2J5shDsLHFx4lv"
    "7Q3j+6usBkGb8wlPFhPBlFV8hwFtK0f6s9AWTTAbe9mp4PsSWdEXDYJbKG6evXWkVRBcte65UIKBtme05CRx1EWQNgZf8SLo"
    "lL4POdLNg88byQfdjh93f+0UPi7yXud8E/PmSePLD8wWgnHfsigEdfEE06qFLB7Myi3mJYi7Hu9VM31kx4972AC/k1wdyHO5"
    "3kQNK3qnneCT8i2SdYJ2f9+cRjCLIu5mI9+Rl6AfEwxoQxe7cUB77gok6Gi0CS0zuMeVDYBB1cJQ/tpjbgRLmfQ7Wb+RaAze"
    "b4auOvHpxpf3/W2XcJMg5WGdhGC4dUujpWqoQRHtzUbrScklPlhiGuxO/r6iEWwpQHEiwncnGm5Y0ZbVVf1FfW9/WP0MCkHO"
    "FTRVB0CXh+CTZhLLCGkEX2f7mHlmdputhFrWx3EPwQfNOIlzHeJSF5n3WtEHFIIezdV/nNQBB7euCIzoidNG0E5aELda0SeU"
    "TKaY1QnpCL6mJ7GaIze2U/dDbeeA3+EyTTv3TRrBowT2UXUhokbwcRfBNzwIRrISbGwO/c9bbe/T5KyX61cFjkGqbq/d+HaC"
    "zbMQQr3VzkwqdpKO4IcNTo7e8reekIexP23NvfacwPq7LWsT2Wf8ENOTYcno4ePT1Fy4HVkIPm2aC/N3V3/py7ThGmm72g17"
    "7jGY2K/D2l+Iar3gf27cNFwcHcSHoDs3t470I211qRSInSRFatGnaaNhV0O/I3AebOv9l7fqg7ZO8GUjsVbsFeVDMPHvljmn"
    "2RhIkATG6+yAtXo3NG5olsuf4Ju+3o/IR3w6wfwpn79prLIkP1i9VsinrttfjiCTFa0QRC3xlGM/LV0cz49g8OUegrgozG8j"
    "+Af1501OafQ/t/p0PgSTcOLq3AtL/QRPmunE9kjq3k4eLfJ9sB5fw4sNYnRYNbtelWDUsMnx3T/bMXROy78JwWtyEwzTMCrQ"
    "uhxqfgRLg+ZhP8E0594YhGtu2kuaA7TFb5d2uBzBzi5olxcf7LidrrVanfSWHH+W+bnadigdA1uoUX2xJvgVn+L+710ber1G"
    "j0tsa55sBHEpkRg7L37Fea2uu0XJtr81wa8KckX9RqN/K7ebqJEZXX/IX+Dm9GkNv+Kmh6B1vMQiPfMTHmn2C7fatFbpnyRM"
    "fPqj/HOnLva21bY01wjDtJzUqUJ3e0Kls3hTzzk3K5quUy6SXGOdyFe9y/RqgyOdJu+Vp550IrilXbkjKk6lrc2itAKk4d/P"
    "swN0nZQxF7n9jGmqwen2S7fq+mQpf7c886S6rO3eEWRFqRUudmo3q73xnMypxQgyeWNxCBi7y0510GY54ay+oTyJG9rlm6LG"
    "IE1J9er7/PySkSH9IgQNll0FMcGwaXatUohfXeTUHfPunATTU2+CJQkm9wcFixC8gTtcUMoK2NqTeJG7MFZ1RSeWa0xdbzkd"
    "0nzPyeKK4VlLLNWbNILZMPOp6yfrX/cyghGF4L9hPHfEz89FVH8LLU0wfn3LW4TgNzDFYX/YTEW51YnzVXGPw/3mMvXl7SOu"
    "BHsuE/AWnQILgu4iBN0mwUMrSWRZDxp5o4LgM3Ka59yS0/Oi3HXxtEvazqWp+aVaSqZvSIaTCD5ljttxZ0hvLhHQW+UShNN1"
    "DQKixM5um/OapEnCbHlTP//U6f/+GeJMrJ2sNVVfKcS0TZ6nrCwjuzOkX45gWHbK10YrQFWn02+boBIfsFwmfX5CPtibzxOd"
    "SrC0+GFPIrjEhSGr2GBF6yzriKcVo7QmmL1h0Epw9YuvnfIEdhJvFp2g7XndyLXJjvp6jt1ZZ6EvQ9BBaVFhmWBs790vrh/O"
    "KFJ/tFRJHE74NfvnT5yd51Qx4qMJy03eQmPwZtzkp7SY6k8KZ+JeMRHSOmmQXMcSFPEinkrQmBNgqfIwzxCOTMosQvAgJnhS"
    "ynLS9KZY+LYpof8rvRxNmMl8+kohgqUR//54nzYUcDrgMLfvw153LSNYGoY/mQJNy+Gddeuvfvn/dJUhWB54709aIVyGYMCU"
    "/QisguDjtfMX7KHkqA/XKqe2kx7hTrrT9MuzEuS0E83Jlt/mjuh9JoLftjM7iTKbGqaGA5PAzmsPg3Lqe9o8aJNnJ/MRPGb+"
    "zSfdBBfJqmE2gmk5wrtFpJ3+LT29aTo5bi0naDyrrzWN6VjeXCdqkfp5/qMz6MsQNNJje3v1IIkw3l8TzPy3e2k4H5TvHDJC"
    "TCZvBTWdGTOdzEm12u0bDYK2vwjB/tgr+kIc6a5QuUa+QJ4ddHWWu2F6KfW9PgSNa15NijHodDpEmrXI4ZROP8HVgFvNSmco"
    "mfMqBIvuh4qbcl48JDw2tQ4g+OE0gs+agVMbJNRJcIkV3v+NhWCkfT77Px1uWDHsrNOVnxPMSXBiQVOAaln69qjdlI5ghBmK"
    "1aLeRLOfncyYlDcZL+ICwBkJTt68Uvr7TmdzBGZnWm0RgiFLuaHb10TZ2qGdvIH5koSXp29qxWfMY2gqwZLb291xItxNMFxg"
    "Gsxv9ey8yvX+ced8c7Y+YjD5Fzon3tbvTX42n7mU1Z1YYlHm0hPDoE5DZJLHFQ9uTzxBk+SrRZ3XKeexGT1z7z7OBqGZms6P"
    "k5BDdsnwmFco3p3otr7k49L6cTLQnXsIRtoVBo86My0BnaD32XzbQJiFEzyMieGyjsHwxsSm53RCVxATnHt1Aofa7+L+qDYj"
    "GNIJ/rWVb91JUxJmdIfHs+3PdddAvnimIsEfw2tHpnMMhp1jMJk7ErcoT8rc5GXjZ1pe4mhFZ8/I+NcQQ1CcvWIbQZQSNNcO"
    "Lq+qu/nSMqoSNIl3k8VUneVxYVc4W5pdtx21BiE/gnNvP0PExQOWAChb6I8pBDXCz9OaV2d9lcW98+ACBNGQRZxmi74oHp8j"
    "wTyO0kWY0Ycdo4h49jSCNS/8UDBAOz5BBA/IWBlt9jXPyhhJQhtPnQZ3BE6EXScAnVHPyRliRWsEbwgm+JOkP++xeuGuX/nL"
    "0irbC/RfpguDkwma+WZuAUOw+2yTqQRriVHRZ6Ybgab3lrObnbc1PKIsU+QXZ0x4sDe+OIKdSVTXZjC27AQNwQTva/rf688a"
    "dxJ8TlummL5UnS8vCrCikca20PRgBEGzTlBwEbexq+m9CanA7jzQ+BllPuewyIKD1J0R4vR3dYvihKcnowjW+65YgqavOX/U"
    "+1io8/C/l6mxweU+nh3FPc3HeuCJCukZz/TlQ1D46sTlO31t5HUf3+jbdYLxNb3n0wmuJlR30X2dw9PdcTQxe6nTtbt9bfRi"
    "vU2eOh1mZQeoSnByfvfHSbL/ac7zYPp9tH6C+uwETRZjkozBJ8TXaTNglEySlW11q1BieoY+92uRQgTjij1vZoIMwc/9lOB9"
    "8rx6LoKdzRNOI0peOSF3p+YijGA9sywllw9BsSu+O0xrZ+dG6ltXPICvWafp7JfcIODXbo67O/3ZUG6XVCJoNJbodcFmlcFR"
    "eJAOsPoCsLsiGMS2M9mFXyEYvadd45LxS4MreyGC3iiCTjNpIrbIgoXg39DcCc+8X6oerRCMfbLJtuNS3G1ik7S1KEFviDMc"
    "n95Sf3EjXNqR+T9M8oLWhu5W47r44k2i6YGsfZ9kdd9LEUzKn5xB354UjtWaWPByU/9DOSb5DqYu6JYJerXRPOGRsgINFC96"
    "RM4Ca4TlwH/gPLxqk+YgEerKfJLBMLxDPJpH71TGxo9+p2aBxjuhyVW2+oOkNCfUFiSYOWVDIlLPPqdUQYgk+Iv9k7NF3mRz"
    "Aa6Srbzam9P6nD56bRf7qXnPju3VFowIkxcZEs54KGzN0YtxZPr7V2gT75A00i4xos5Xm+CCvi7Fqe7SBIetFwY4akbcIcNC"
    "9mh9qjSocBvBZzp1GuzOBkxxrrwizPnugp5MBmUYwbD5PuFM82DLImCIiKtTp8Hu+Wn09K1XzseONG3J1CgZeEQQlaBYZ7QY"
    "eC1nUscEjZYx1unCTglRv1l0j7gNzhZFOISg37SiTAT3J6auEp21EYy0FoId1b8T+p1Bsuua199jaIsSdAe4Mh6NoNAa4L1i"
    "DL5qMSIWlWDUSjCtzw/HR/QZt2Isbx0uOhMOcWU81CBoCSV49N8VBNuK7i2qPx22EnyZrSmMlpVyw8V863IjGIz4O/4AM+rZ"
    "ZF6C2oeFFX1Kf6YfWAGNoF9ZmQorC8LT4sHEsjvlMciTIB7xlwaEM36ToC2SoHGIatNX01r+HZt6Mo9fSar61DE6Up9JPdmk"
    "rT9MrLWHeREcdVGdow0Zg06zPwok2G8fwn2rTNAopvcyQZcnQUTSOo1Y2bZ0fjF985P6q2EGFOu4zTFIJcgjVaqvHFj9awxJ"
    "JcstEVzvlHSixE/OXo1y1Pq0dUEvs6Lsa2CMetj4yT0GgsxW3GnenCVsDMbXlOmnDNP4F8sp7LW78yCM5+h8ffBfUn3VSQTN"
    "UlQpJLWdR0/3GQiy5hSifBt6lSBzweHRoIZymdKiZy2pZceLmzpE/CP6hJeXuUmeeIJPesesz07wth1SciZikjKrfrHNMr94"
    "LQSTwUI9+N3gQNDVrrz9drFINe4yie5InG3r/EkyI1xi9nWpBJlTjIO2yVgxxL9mcKX/E2r2zG0n6E20oumi0pXEjmavbvn4"
    "1XC/kxdBwupKvSTu1Tu012H1Cgad0m1r2q8zLNFHGnbaCf6r3RThaWqT9Kwfrn4w3pMxyotKxbgcsSfM4ZAS/69SO8RK0Nm+"
    "OoXgoBr934izVT/PQJA4LUsTq9nB2baSTmqnZi7t9PE+mQfjczJmiWDx5sTIxvtD9tZ/wGG2vM9M0N9Fwep5r9AIslukn2Zv"
    "qHurefA7DLOLX16aeF6dB6NigSIh+CQLJBCZsmuumGbJBwVXI8u3DkjP/CQHgkaavmDYBBNfbx9Q1myHxVbb7O7CM0f7uM9A"
    "0MNO/BbpPXVaxYomWdzLpWTHaUbQnlQagtdDnGyVyy7zpAezPjEdYHosQsBAMLqbvvZEgtfZZ5vA0UyWEwE9O1ldSc82NGrz"
    "4F9YeWImiSsepyNkNf9MJZjFhWHFRX1Byjtsp/qiTHqT9nGGWpnQ1I6pPufULHHrbPN77uobGcy7e5zMJ4+p0cS6kYKj5EVv"
    "bMdv/INJ2z/0PBdjVY/HQOSlPcw74XBlRZaycBnSj5dWD+xSXBFRBI2vatpHWSJe/0Oq353Fg3kjJeethXv7yQDyNXNC3s9o"
    "IbiyUebDc4c9ug84JALC3OIwuHxpreh1WoccEFsNqn3awiwEEW3dKcryRfkGreR8z9uhlt4H62xP6VvxOae3tcPmGAw0FAw4"
    "5ckLpifEg5MsrdFPcEe7HEcStycSHLtA374Y6lOz91GtTCaO4qMvnmXLQJOMhu5l6P5JtW4YxaWbeYaIZTZ8PuIwisYYPGFd"
    "5I22OiYFUecddvfmIpH1nE6w9FZR/Cvh586eTU6KZi5MlFrTEkEdna3++SupdXUNJoLc1hMZDHLUNSkM8gsGzEBWP0E7X5Co"
    "H4JbWaJPp8HAfvJ8+spE8sFRlPavck+w3SxcMhnXXFlipV4umA/BAQmOIfsNf77fDbNrNrVMsDyEXyUEX7wgPAahTsI7ycf/"
    "sDIyvSLcYNqb7SMOgzCfFnonTKOTYDjAMxhwjtfn+l/ALsKdhi9q1ixWgF+8mr6+mxI8WNduF2GiV9gOJn+GxZHp+51sDEa9"
    "q/RO31TFbhtRMGS+YUrNZ/nRxhOX/vNFanbTMYgmbvWwSHRba5w5vvqvPO9/k+2YGZvB9PV8Tu4M9P1ebEMPOwmyt4nNSHBL"
    "2xuSuq/XnjvNeXTt+pw4kz2sQNt3qgT1MMnlrnme8CFoMcWDTAR9TgQ15nsbt3qMu9dnNfRqP84r+f7ZH0+s4zH/5cp9f7Ga"
    "xioEoyGOdCKGHvqByTYGnT6L3OqBmKWVclaxXiJumH057Y43K5WQ5f0476//2NMmEvRQWift1MZgfMrcFjtBhpxMz1LHmzzv"
    "2HsjyaqzeZ0Ov5sXJ3HLy+xtf/JJ1eFqEDQ7H3jdivkW+nMuwWDyoqa3zo4WBA1PL70dA8HpZaZBTtDrI+j3hWzOgLUj3WM5"
    "huA97SNPqg5XRU/zBSWKy+ZVsraNDDKPWsj17omSFbW8Tzh1L71nWWVySgazEoyYCO4yvjyTL7PynF50EFw5Cj8qNcAxHRFu"
    "H59ThWutohPbw96gedDTI/bkdcufIdbY0mEhyKqIYZnQcPaOP2zkz1r9OLsWzRe1kJSG48BPr1TJpGPQ1rCLtgcQ/FOmUt2u"
    "i+/ezTt3/3B2eRK8w2BuDVd/fFpdhSjr92tPfNzwYtrzclyyuHuoNgbjYuiVQxENIPiGRJ9liJM6CHrsBL2eiH5Qq9y0+3/9"
    "4+7H1gQpKeCTk+rAfE3vbaYwgl9H1bWlpKQjOCrKMdmCWWfaPPg4J9hfzRDwJGhF+/2/8+zBg6e0SS770WnrTYmR1u1OcFmP"
    "3tfq3RpFB9rB9aEE/3Ja8cWDvB9H/eaYW1YtqYHpLxUzHcM+bY98jacnTOZiiF892BetvHQS398ujmth8zOf0rCwJ6KsATtG"
    "XY1bRJ/lfnt+QzvEmS8aXWkMN/9TT087Y/lSOx8zutVDFwmDy9V8b/zNt/FAgtPkDzmDwedMsP8v3EXFV9d9Sr92gL3bNmOj"
    "/JDmwujyAbhbv3MkIbhffPxEgmyXfm795oDYsWt1abBpshiuEl9PBx80N3C+aifolvKqyZqPVUnIkHM+BI/wCYWgXnz/RIJs"
    "y79Ddk1F3QRrJqWfzlnPb/za1pqg39pFI0pOxi3FbLEZzVJXr3hGgyv9HK5NLChpIrwe5BOXb9k2Q+2+NeAjnY46mTikHuSN"
    "6r1jUHdweW2vMS2nBE+amdPyRyQXUNbCDU6OzArYUe0H8UcTXgQZNeRb3G6CA6MsHPUtXxSfTKsov9cW7EZaZQx+ohEw8qnK"
    "2kX1CRWtJ2xnNk9moGHuITh0IuyMP/a0PzCb6/CNpTXKkWI1I/njjYHMyYra9Rb5VNJ5YoLvSkowaE/Rj3HxultyR3t2v9NS"
    "ZINvH9eNrNNSqMF5DMZ+VljzCIKM4J9cDIKf6v4LX3x/l3SsTOQpiANcW6qP+kptQj7XDOlP6t9lrQ9b+46kBKPWRZZRxsno"
    "HAwH2gdvdz5N9rU3Vu0UmB3522Y7+nwG4et6py0I+qyZ7bnVvTgxnGCXN3rL+IDJm45XXtYnpH6CYihs9qXOwcuD1T6YHLRq"
    "FQQN2r15y8rhGdLHvXX1z19ui5cZb4VLxt9+Xu2Dm+6RLXCBt/pJxvpkb3/9gkgugl6nMzo4zEo+UG/B+x1GI+RbpXDeNSKt"
    "nyCnG07sRovoJPs6P3ktvSixktyVwSOd9HjA6BF9QHzyXv/Ln6TQSHo2RfoIewwE+UQT+6j5UdjJCcaHdujJBStSKeRLMI4I"
    "zcBvKbE47C0USu46SQjmBfceNXUiZnHpkEIQOfllWsmVQAPvEZhDbkt6aRzBrRu3NONV0LJ+2l81kGx3TtLWIRpAkNN+419+"
    "+KxhleyMYKgZ8aNgXzYr2gLJHtu1r9/VNO8OtYL76PCofzNO3DxJKWhO0O0IdtY65xNMHGIPNW6VzqLjICVou9IRDLvG4HAn"
    "/e4vum33whuPvV4DFAf158m+ufOH7c4yETQPasQz9lq+LsjKox21CA5fOCVXjzRjmzZw9K+avVXkSbLt9wKtJ2AVFUxoOKQ7"
    "5m8SgreG1MosHdP/UkoXDSfo3NHoFxlsPzNZ9g7Ga0xlM9mZeF8PXU4EDZ8eHJ8lE8p2QXDUucvzToTpNHgwuA0iDbdF+18x"
    "2bqvQ5xugg2PNrzNB6Bmfo/eYYKyS2CWZmmJI0JzpI9+tzU1+tY/MtnO/vbKx1hE3QTfTSrAo6tc+O3Fp+5RCYa4NNuY9XKJ"
    "UceQzrM8MYKgnVzNTIV4S9tli2/sD7un6VJM8oN3OC4uXarXaqW7B/VkyJUJvk6qCdaWNDRldGUSX2YEQTMxfL/WnTDvGYN2"
    "z9OVuvyr5Nyz13ymQbNeJ5Jdjpps+ItyyisT8Co5jc/Pwf2FnAStcQRxQvCIXiTzpDuMyAma3RaiPA2eaWhF8CWfeVB3jKrV"
    "zlrgWfx0WTNZvvZZ8jwhuB56jr4swah1mWFMvhi1+Ub6nxnmiw5bXrgGpR2E5KHfPZLPtI++4JbXXj3k26RqT+LGMbz46OXs"
    "QfQw6UAJs7zTaQsTbJtExhA8WjXvffrQtT/4t6yOglcfrUfe75asKO2AioL1mzjf/Gr1b14Et+JjpCtfFP/L/9Tqpf5V9sNf"
    "NdcE10Ng6QgxaB1Ng9KN+lactTC9llVe5N60Oye/dQhR3mFw4ndNg3685vOYiDpALFvvxYGGHxdfkYSDZYLe/tK1F1GrVzks"
    "qeZquntH9+kNqhPnbteL+jfWocaHPY9Wsh7xEP0dIup6kyzZg33Nfl6kfZKkbXkufsbvgia+ZjTxKrcGvPDKoj1LSz4prqHp"
    "a1c/3+VPUTeNBz0EkwtIiKgrZ//H1JmLlyPerL/kVrL8XCb4148kXWBKTvkbcBWBTvQn/mnQkkcxgys3Pt+/Ml/b2etrnWtL"
    "QfJ0J+SPxBDMnLns9pXMHtyKe3ZUJhgaixP0qguaJYK+NqB7ryaL0I5aeoR99pme1EWQnJlXvarPbV35EnXberlCZDv+pr24"
    "Ej3xXg5KrnDl4sudxQmWWwM/cSo98Oqgif9bXQtCQe90HHcaozdnK5Rg3QpFN1bvtYpvVtP7jba0hLb4PFgZZ7Z/rSASDLiJ"
    "IO6np/nI2aP8oddvCv6WZj3rtaLGXASTGTfexeGZxLGCq20VAm/kWGDKj42xAnRzVDhhZIVKJzHBa07TMe8rtAyayw4+z5Tt"
    "uHCCpAT/+IXbXmclx/LEZe36pax5wmLcOMPm/WdJhsJvHNiWgDnvfYrGlZB+2xfNQVDXy+m+0qLnv964n1OCUUi8yzb5/RSb"
    "v19OUg8ieD/JEsYdopqpZFqUCC9hprXLuQhu/1VsL/NT7PwrRbpmp16q81yWsbiv7VilxhlGMB5nP594JLEV/u1qY6zHGY/V"
    "ZzSTFb1aHoNvyMOyZ1ytNngsC0E36VpBqaWcYQTTTzG/oV2z3yv90Y420tx4PJdNRvmiJDymPs12eRBG0pTOpBuGysffMBO8"
    "lRjdk/xV7XI6xSRfy1+x90ZGSx6CW2mcd0yfle3H5YSSXApLfZBp6dQMV3NTcslV7mlryXrazrrF13mnXoJmZVpZdgymqyWn"
    "LX6VHkpXtNYoLopLfLSj/tQojgkm80XSGV/HpdevyP11Kvi4AHfcl2U3KgTbjyD+/9u7nt+6kfs+FFWNt6uaXuyicZqNx4s9"
    "BD3Viz1UaVyPFg2aS1H/B4XaHHKsk0sMVFlSVQAt0CAK0EsOiyi9F2gOPbRoUVFRss4CCygBesihgKkojRKggKk4iKmY5pTz"
    "ixz+eI/k469HZb7Aeu0nvfc485nv7+98v4NI0cPsw3HF8FfJuRUIBtbSIghofY/LQqPmXCM0BNZjhuCXRWgTmMfkwJOG40FZ"
    "Jl6NrCs65Z2MYeCPasncPizZl1eSbH0I+Z1yf/muhbqKuHrmGhQJq0KK3oIsoMnWEuGQTSz3iwGM8nZTKoLPM6HiURFceeOg"
    "JAtnCCRpeb6hhOSXirxsMpNuFqpY7bfUc3j6wgeHwqbNfnJODYozni2ffaHcwA7GjMmYG/dL7INXBJR2gmCEXiwbgn6mIsUN"
    "WYZ9vjf/eFd9f/wJ4mPuZD/5fJ7hKTfKTnv7jhtVu2sUt8VA4m/soNvLaYummXEeQ6YuRRWC5ye5xXJWrigB2i11aXCElkMP"
    "Hn5YVIOWlA1M2WB5ZJeNnGwQN6jst2X6WTBYHcltUDV5vrT60Edpr5lwzKhaTodzw0yqRo/t0tIi6GU9ojmlGHJTfTNrpNC1"
    "gcoS31IE1YLfaEwpauASIao48U4iRS+WDsGw5Bh6Fd7vRWa9sX9/6tQs0s514drZL3NsFLpuD4Qg+XXhWJvZZ7NnmdfLoQit"
    "zBPP3zKUa7PlGrFk3axXCRvrk8+rcf4TMp/z4UA8uJqVjm7Kg89YkIn/y11iBKGbMUXmilFyuJcXOcT7m1qtV7yc03FW6pqO"
    "kaN//a2iHqSyP/gi+Q7rhmvyEPAyEkMLehlFOG+tn7WtfPwCkhcfqzUW2gFzLB53REtmJasFPKGDQys4ogNkXY4grT48WT4E"
    "2dPaQYYH5/kTx4VW7rSjyH51OIa688YcBL0REYSP3y82d7P3PRRQ+GhH7lgNXtBbHo+WD0HmO7B+r+lrP52fnifZm5Av8hb2"
    "rMxgRGhl1VdmYO2PWWVBTlCRB093kX8ZCyQZknHgUiIY8riRq1YThHMRfJJDsBCxfzo/ko7rIwgGs0WfnBQRDE3k2YSF81nt"
    "L/3zbEkRZNMyFGa5MQ/BYtrooIbvl8pnRV6pRb/+iDEZo0wlY/L02Ht6DsDjF8yGCZbUkgm5hxBmVhHMW2vlOtB8ras4Wmrz"
    "2KJLvwmMgXjQLFPJNjk9DVaMGy7kM1bdZWt1qB44i0Qrak1WWJHMbhdJrwjRJrQ1mD8If1GCYKwOQv+2ceECVloZgT4LtqMW"
    "nx3z2zVaeKg+X3RnbnFzSwhxPQRNX2332bM3AQvWHb2YTYK78FnAHzhqvfa+EKRpdzbeG1eZFV0haNVEMBgMQWA95tApCLKr"
    "bsE9SHeGRUP7vUOP2jQ6Ce0T+rSY1ICw7Sqc2ZI4Hwkyw+FuvoALFcFQ6MbYmUcH8XPZT6Up2h/B1lo2yn3CzFqnlggaxDfq"
    "ufQGQ/DgtA8Eb+f+/eY37TyCBruRZyXdt8MY0x4Voff79ztG0K2VSUvd+roSm3YBmRNbEMTcGYagC+70gGCB328ikUhSEfz1"
    "C7IbP+4DBlz4/dMaYx4XpucRbI0gmrmf+QrOsu2vi2B8Atw/rkQQ+QxG2Net6zzdeIsoCAaph+HhcPsB25mLR6cE9SpH235A"
    "Xsx7jdyJp/W+xIVYtGbmxNXPL1FecMvekT21rpjlEUYKgnyhRybY4BVqZwdHvSL4S9SaB3PgxMu4V6oIn5UKgZpqkLvo8Ekm"
    "rCZy9YrgRhEYlv5ArR1hfYS5sLmx9taOzx7v/F/7vUTvtY4XFO47OmZ53+Q2oUHAz4ZxlvAg1d/CPMrcv3AHhhD+R2nwb828"
    "QKd8b91+i0XbK9moZkdk+3nbpwxhKM3Rp7T2Xn6zpyLoD4xgJrLmJTz4VdNH/qsokR89IogP+koeduvSc88vLdWOGT1BcD3d"
    "TjQ0gvaOEhxxE8/X3XHxr+6yYH7PnUj66fjldO8QMnFpKGeEeHY07/sGIhlxYQh+TSIYPtp1UPSUJbXf7hdB4PQRMch62MKd"
    "8FCH3+ACtcjIHw9BKRYYgu/LoxpYN4EVPjpvYG4vSqtgr28ERdMna2GNHqIy90ItZA9GRFAIF2Z4smZJX6CP/JfXbZHBPugX"
    "wYB2rOpZimLSMjZaliH1V0qisYkrgYbkQax4Nq7Q+NH21zG/cxbAZ70i6P/FKe7+U7MBEdLSmAnKInLZgLpwIRJX4t0hefCd"
    "ozTGECXLvB4jSIdh+tZPe0Xwf17vo6l+Js5leS3zvGEp76oIyhOT2sBGV/Bcq1Fq4Sp1MIlYjfUiu6XqW06fEZkI3OtjsIVq"
    "WGAVwcUM61k30CQdy2+w6V9YZyzYVf4vul1tjTpmWg/qyiC+n7y20ysP9qNle8vzzvi6LdaR7oEoX+3QtYC1zFxkpuHlKCNp"
    "AtL7oIJ+EPRAT1lCUnqNK3bJ6DfigJpQnY3IEimxGgiasRXziJBfSCY0Mg9LEQzIxKhPBAv9jllMwgVyvqrdIQ/Sy2XPqg+E"
    "5TJNd5bYAOnDEn6BfEnrDRdBsPVH7zk5vR2xy8AynOWBL1525+gdHdI0SCWERsAAQokYTfA6l8oRTgxBt2aF7CKpLJD3PFl/"
    "fJ9OAULUK/M71YK1wgUmD7wfJL4wLLjHU0PQ6QvBGKmLvN9yl3ljTzyGoN9lgtBIj8184h03cLJ4ZnK/i5VzNzEEL0BvCOY7"
    "IwQAvki2CRejCZ3U1FemHG3VvXGBGKWSPOT7k0NQYcHrnVZux/QPOQSREou1UwRRJ+aM+PCgCkJaAhJJK83nkHqAlDoYUyBF"
    "6kB3KxPfaJ/JejLn3KQImp1MCFmrm/pYg8plnJBDz8cP0uxu/G5rOrYo1emKHLM+Sv56l/Xpbvv5PzmpQtAXhXE77fMVb5TH"
    "ecszTOdqSNGSfuu/c8scn5OjnWkgGFrk69uKR/xjxTf+jd3SH4zf7PpzAkE4EeGofBxTc3++pi2DlAYpXl5o0pkwZ+Ho08/q"
    "IviIuOuKKfDLjCPoL4ag2Bwag/8wf9PjaQ5BPylOPXY7UoM1EDSUUJGXj/969MeLxoSHl6IEeEnRpqH4UlxHNe/LsZsmeEub"
    "6piK+kWJ3UgR/FFLJvzsu3UCvcWIPXuCt5P9oG9mPREmY8yEtNWdl1iebiYY07iz0bmTTo4si+GqrYKUUWyd3F36eJ0gUzFa"
    "qDZ22rvgW2A7SzijfrbM8yXroTSgYS52R8oDgTUXQQKyCIaKJ+d35Q8S8vdVvwkzQYbkrWwobYzgNpgSgow1pD2RmHHBIvY0"
    "7Q9oyKLkyvlhDkoVFuoEwed1pWimmYBSjP9AEUP2pBBMm/dKBMVVyYYUr9u1PeHnmVXRdBQmQ0hQeMdujeBXntZGcA2TjOuR"
    "a67WW2p0AASD+ZfPKj/GlmOvPVj5hVaYXDizHJrxbRvZvshIxqqojLr0BMFQygVzYggGUm54rR6fDu3lyEVrT+anQ0xCx4iD"
    "/F3CVlJ056SuO1EuRQlz7KeJYAgE03hZz6oxDxoio1tVzuPQ6XEdZufB6qcB3Nmry4N5dyIpukgGchiTk6Ji481wcRlKxKRw"
    "S3HrZ8ZiIQmg32X1/e0jdgP+iaLK5uAtlo1FVEg+bWAllgyeFoIyMh+RYLuNCHFqZjRooj4y/7HTOtCvhI55ygrOavC2eAx6"
    "bt9XGM67jiWCE0swpddtL1sxoVtPhbAOMhHYA13eHvy57cId1kusBoJcY/JhGqup7+ffQxJBtorD6SAIs5qdL6lZu+LIlsm+"
    "apa/Qw8/WDOc7iwZw7EBNMNbuNa1DL5A/mfqOLGm/K4St5mOKHVzXUdZs+KG2jxABNteA/mTY5WWvSwMsA3WwMYGOqyTa2TQ"
    "BJknjVfr2vExVEI8/zUhBEFOEvJwd6NrvIG8Fl9Xi+b87rYevcFZb9W6qJMNRiTXbjO8w6sN2afgiDGhMx0EwztpKNPhBzBq"
    "alIHDWsU6Rdsdnq5U5aD1i5sy0TOYgEaI/hD8cOAZRGrEVyWMWkv/o2t4Y0UiM9QJFcaGaVeGYKzW8H5wNxxQPdUD8Finwde"
    "gxhIRe4AuFup0v0ls1kjoOBAEbxhNjphPj++mVYCMwrYnzOD9MlKDwiatX5pxg7QOBESi1mpTlD4S5bD8MyCN9wsOrPFp4yq"
    "L83oaRJ8Jl49Ci0XjEQzRMN+IkKCOk6hf3u5wm/Up8hUCfmfbx4hZ9okpb2ZYTxmvYdjIThDw1kJtrWMMr9FCLIXHszd3nqz"
    "yZuRWHbu2M4SMgxZD5OxECzfd289Bc2pw4MrW0vFhPQiuafG+pvoUCStmSyvGXPMOd/EZCwxWn6y/Btp5pC7ti742yomtJeI"
    "B63chuLGCMYnF5eFzMuXbx12eXuwmb1TbmD5OAOOSaokqbNUYjTPD06TNwuBk2tF4lY6h2OJ0RlPgzP+rRVVIRgtlTXq1pAz"
    "M6lc5J4oPEhL+X6QbtC/KOmMEejvDsoMLCMrIKmlVRdBbylyTIs7ElF5/EbtaBvSYdO2EkYtZfyRbZnMeTbFMK35YtQSruTE"
    "EQw/WQrg1kwEfZBJSA3eqOu1s2oEDVIdWhTXRe8vxQR0sKgZQ8pbccWvbioIxlLUMwoa0uOeczQ4D34uO02o4L46IjAFqlxC"
    "tibrZ0sQBY9qRS1mLYRUIkjIQXpLj7WxSHjQGsGiiTf+qOQcJhU+FDw60M7AVQF9zE7/ErBgMKMCerFsx3doRd9DKYu/Ff/j"
    "SWj6aVmfWHIkrabBLZrfIX4ZNhkEsV+pT7gp4y9FhLuVKZojeo3NsEKQNmaOxeWm6UPluNjpsRkDQYONWSoevW1FuuOgWhq5"
    "rL3KMmjBsI0aLAlV0Ino8vx+W17HSAszwXWcWk8xsMbAtoyByqfvBUI5upz7woroKIxXYJXI4/FZsF20z0tKX6xUVBrgUyqC"
    "lpV+K+2TNbg1ejzjJNvpIyOlGPG87JdfmBzBZXAGI9ChEI0yvOyu8r++S64nJyPmQTNFMFa6zvCu/YyHt9PnEhYWnJknC97k"
    "UvR0GcLaHbKgiuBK2ncL02th7OeHCYKJ4Tu8Hpyn30LpE4cS6/OjAs+esClGDEFvCcLbXbHgfkYkmw7rYChgSkoY9umBMSTU"
    "myB/h2IYCOf0GbwmEfSlNPWKp3pXLBWJ5Liqkob3DoM2zmCJT+wll5JgomANmRCNTHLhpgiOlZ4AlTIEy3XgXZ8jqEYPd9L0"
    "i1cYpDP4xQu3KwT3swiS/1bvNgg/kxo0jmilNCahKpWSQGkC1ocxM3BFtIEK6euFmJo7dMoirFeEUINEHy5gutwGCNURcg/5"
    "R4e8BVD8a5dfk/w5eIT7D41v1s6z8U62xgeGKA8RhxQnCLrFw3A4ph1TF8HAnoUg61TxA2YSearxJxA0JILJZhlgaAivPVy3"
    "69nlEkHOlDC1HIRHaxemOpJocDXoNEy9iKNalhEUJ0L66xazkdbFh7oMt1CIJzsRtzcFzw5JNzOrBHPOM3t4IVNccJ6ILcSB"
    "tIr9/b3+M/fZfN7PaztLmZM6w+f4NbDl+0Fyu/omm/TgsCuiMYKhQPBM7A8YOiYDVrPnVNVb2fNs8XYXwqdNyp8cbrGHPBGc"
    "ZefICsz+FR+a6UrUNGacGTAHytvpwTXPYkzBTROy92wRJkU98TsUN5eGkHfbILjeuuRQnY0a5uWRU/Iu6RkFbU2/xRE058r9"
    "WvXK5hyJbKe7wZncjF95AcAn2KrtRFYDfmupXY73+iJ6MLvt4gLeUWxdbeYRLKv/kqEaf4F0eCfkqQ5L0KAwXQXq/hyzFifs"
    "/SqJ8P/xBcc/e4lx5utJAsvlHNRuEuH1zdYFa0LsBfZvtgo2gV9E0AdJK6qbYIzkYJRxOd0mYUMF9VX7eGZwJxOdYB1gDYbg"
    "hp2wPBIMuxID2g7BhZoqOOuPXr6V7ghH8MFqiTDyionTBMqAStmhWDCCjxTMzPlCtMqjYKgT7x3Cp90QH7Kr3GFeKzAE94Ta"
    "8xhugQNUIcoMGdQOwaeLvOvl74Jb6d7z9MJ6GacWGTdUECxRN30FZEL0nl2GoLcIguJmhSERdKEr5xBk8tWs2wD/5b0IfJZ+"
    "7IGbIOinB7sVgmShfkKbbx3v2xkXrlQabRTtA28egiH2cE8pX8jZPXqDPqk1X4bOR/BMvImO1HQ5H0MWICzV6zLSTzP32+lt"
    "F6Wx2ifaIrjgu7+0mTEicc1QHPcvEimaC2j4mDj4cS8IIkecdazYmsECBZWKef0S8fAF/ZR16tb6pRrUv8uPRPy2V5Q3Y3LK"
    "tCC4DXbbIhgtFBDY8RVFHv7GdmCNj1FKQ7hdrS7V5KGqvvKFbO/oM143ZbnmnKbUqF4MDoUglpQ+/eBPRaVW7J4fMOMzPjfm"
    "C0Xr8vZDrInF/bYILlbrdg1sHiSZ22hlc2Wj2n7dEkdeXjPI+iSUL/0hwtfYlwC5tWztObnElXvs0iAwvBmeJK3bhre4B/ZH"
    "hW9clRK7JYIL3UQ0YiASpX3p1LnYn1SDlCIIlOB+r+Frgwfu1haoQvBQIWbhZ+PXZcy7/5/pR6pi2/Tv0PdfkNYILpTkh/Gb"
    "oCxWrncGbFe1Ey5kBFhsDuwVwfNAjeqC6vuz9gxHspgqXbNVxoIz+Z/95Hv8t16j/Snxd+Ov4RK9JYLRny8aH71msbR0vWSz"
    "FakHNXgzg+ClZ80K+HdCu00FjVGVyVdBnC9/o9VUvkqw79L50+tYXqFoh+Ci17lXgHMbM64JzDrpZmXUF2aBHNUWDXqOzew2"
    "LmmA84tpMhtRDJKYRQHOFvt8K5WoR9y5aosg/Ai0wn+nYnnKN7kZEfWE9lRN7ZjeSysar+1uKiFoNfpsVfOwwhJyFBsnUjj8"
    "gCT3fEeodUoQdHkbgBqMbOWVjK+ss//Bhc0jxtLgKvSxy8lbd74aDVRQA/63dXk6xKz60RA0/3rftZ3QbHqXEQvDIGW8i+/3"
    "nBVcoDDMlOKhuaVnlBnBSP6LKD2xYBcIwuDnC78XudbOduP8li03NV3njZ4RXEDbCz5xmtVAGD/IylAvs2onbyS1R5Dm+oKF"
    "e9OsGcEaeGhcvFdxmmfwYIpgeLtnKbpACmadbvWfkvcavZcFTkulN5TpiMxZfdwawVg7kWDxykUjMpyNyjIPay9rzeNCrUl0"
    "rQWCAepBDXJhGAIfbDTZztnSO4kKo+pyuUYIOgYJFv8A44azuVYVjsGHWVNuXUpRK8lshNesFioOzomGWlVbNC84g8JSS7NS"
    "8pZhY0k8oW98m2RHA7WrkzHbKlLrG9XLCktcLZFdYhcnwhbVFnNGrATi22YLGSuY5yjApu0m0Oz6WahyJPTFKbY6sGTKxoiu"
    "dWqy5lOYptxedmLdtgi6sxGMam15NEdJ1F7kg3ImdMoQpAeDI8gvFR62QxD2XcG/ZeSOOZQ7byc1K2GLkjVn9k2LoM7q59mp"
    "m7VPaVgeUE2tIPNcqYQKM02Q951WUhSR6EGfABrgaZ7LpXHBkBUI4jZ+gq0W7DTTL4vZqSWSzC01Zjy5zcCQmVz2sBk9eOa2"
    "+Obr9EA87JUHzfJLspGQ3/zCT1sEaWQ8gAu4EKibZiCQBJQP7ua5UJwhelRNdfBt5rqI2YYHlVmGPSIYlnhNIc8uiyO7eNdt"
    "Kikxs2YcM8pun1tLRHQUX+RfZ/sruIgguzvykjBF82XSJDRaSQG7ZzVoOj8qvx7ERi4nEe0ALq4G42Po8esZNzMIDnlBD3OW"
    "fydTmpOIAWYRQbKtxEdRq3hR7uxc6zX4/bxEnFl86+P/LFkkszCC7PPcYkBy2L5zXGhn2I9VQnP5CCN6CztMHzEVoqexR9Ea"
    "QWdwBKFMjSXN1Rf2JqKM92OOhCAuQxAkBgCK0qoA9ojcFA0JuQTk6aOwLYK95jZQ2WaafMFWbMCwk+oufnN2dj8t3xsMQEMY"
    "TiirAhMEuaxYSU8vsC9ZeSwxIPHPWx02q+/DapW5zIbYexzLP4OtDpFOEFR5cM8bVIZmE56Et+4OVWf+TvKIEcCnXPlft0l4"
    "p5UvYOGeeyqIq3MlSw54vRS/FNLKmSjsJa+scAZD0JaPkvFlkjpAUawOPfnLEbjFQglrLzvvmi29mRjBnhdqlnG5WDDNb98n"
    "EWhzizCYFZgcDsD0YqQwzKIvHHJrJUh/7ADbT3mQPegH4M++6t5v+aQWCrtyieaIGKfs0NKIGvUCWAlUR7nbLYngCzLkQA4k"
    "xahEkIJGL2owrvucsJntIBH0HOsLwKtL2vHgrtt2+t0iCJIEQX7LvsVtl6DIDEO7EvLx02bj7qqRIGhKePl8P/Y74JotHp2m"
    "11oHhHqus7FLNK2dSFEYgHYXeZ2cjWSNUDpkKKxHLcwYG4OlXtw0kO8pCIbpdWa7rbCwCOi7S3BZI2mc6kEHtGvomfvkNZMM"
    "33JV8p5IdVDr0EwQ5BNhfdcQWOFMq3TY9mEt1uezbyb0ZyBo5oVf+woY68kIs1QMkvIZC1ME9HDahAe0mcNEexknIjdGkHUU"
    "6kJUGLHN6/TMgiVayeJOIsxY4zNvreAGCN4CYxBWxahDB6G+DoRDb9KKrshmzcb2CVcZAeCpXRd1cNpWM9XUPfHg4/whUYsA"
    "LLcCwdCq702MRBZJzRXixaujJYrcTqYzckmE3eTihJX2RHI60NnrLh+d269DOOuksaND+3DOF5Q75QmJhesIe3MneNWVlxjc"
    "TiCEbKwXXXkJnfkPK+wtOx0gaPWv9M2ZfJIUrFcgeJrr9BylAUZCvrMMCOI0GJrcazfwLVF7sYKT9gsB/7+YlmJ0EXkwyU/7"
    "R7B4zrKNbauNlb2i+Wm2qATtiwfZCDt5LjfuWLLjSDJ32OdwuyZtjuIbXSzAHiJsGJTYN9+uj2DSBIuPtIhUBL3ZnD0gwfIQ"
    "EW9qZR6xl6F8dpvlZR6JS+dt9fj11zf6b464Ttvi5ZfsFI3xmabMlkxnQIXtLFbbVBICGkEzGuXVVdwKt6Ay6c1hf+EhVGZk"
    "t/UoaH64947Pm0HFrta5BU/BE3WyCYIrxXtFeBzbptQ2FlbNOlKm9AqFyH9od1CkZAUAOX2HEfHTqOoI29V9DGToWB7a3y2F"
    "iowzmNEuKw2QURgULy8AcDcpzGLIIuLYHTyq5bv+3bd6DwSH96qNgfMKl4+XJr+WvuNe+VaOMiUczSkTN6Jtg2VDk5/bHXqx"
    "1q5rkst+EYS/whdBo3NcVlr/LqyVRcHjOIi4RpEx6sV2XkcBiRHsW80HoJa8KHru6cagmg/5cAwAjYr6KhY9Yy2POucVlqc6"
    "c/tfH1gIQTcVTtYOWF4S3sTsziC0M5fZC6dYhPSvOKBvBdcaySJJR/VrJnilAXJHQZB7Co/2RhDhvPb2Ru+mWq27GcUI9l4m"
    "kmbWsChGRDAc76t7TxEa9Wz8l4pZiaR+75IK2fH6rtSR/85oCEYGOe73/Jj1Klc8nI+HrsPMFaUALC+hkR5OVJXApjrWbLi8"
    "eqZMAUFFsIZAlOstPcGKsBD68T/tU711qzsEjwn5Zt8hixo+fVEPesqLoQsmQniu6W37Fjk/+DQJcDfZabY/J/4Aq4qqrVGz"
    "NBjToi3TeHItKN0DQNWCmNfXKYL9J9lMu1Y36EI81FZbrlXrams5+BSWHzd24e4Reb6frM3rDkHs9L6mOrZaPq7G65vNum19"
    "Mja1PaLlivfLq5wdkPZxeka1hN8Rgj6+OYC1XUMKmiUOvdLmorJ3FPFiDJ940oEZhSMfPODrDS0raWt4GT/JKtsBu7NeTgPT"
    "Ub3nLUNQnTVXx5T9UIxkGasIyrOBL61qj7emhlIXFKzt6SDIz15ja9SSnVRrNaeAigFkkXCUGAl+Srv8mEmvJl40w2b22NlB"
    "f8tTaFffwq7zvG16TFqK1TpWHSntQJYGJkKAhER3WR+gpCGZPT0EWXLssqbJs2Cf1/S9wPDu3RlN2vyMIRgoJw4Rz3As0Zc6"
    "+OKZl7Q5BlePCT+2KIJrihZt0E6rH7M7zBpvtIZ0BfAJyiHYMqW8CKeEoFH3Wt+cSxLRPL6C1RPNeifimETerAN0srJDF36T"
    "4uVILRGlMmlKMjTx9Zyah7i5GlzjIgqNGb1BtMMKFiGZyGYIAmsnlZe0aYDAzYUjJTNaxg6e1Za4ZSVrFXcEbFGCOdrOmKKh"
    "KRsSHcXQxU9yb/XjhLebsCiCOASTJVxfwlnkwi+pe3KjrQoEQxZ8HIl+j87Y5WNw2HIdyO1hFMK0zjynWyaGYV0vduWYiiHU"
    "uOMrHUM22hl3NywPmOmYzGQ+rnGSXkRHBEyarLptQuAnCZU4j/J68PUKa4m2nhvLCiUB897N78FnvNbe40rdByTto4yDiSMY"
    "fbpJLOltcxkve85SgSQip8zUxp5AlP8gADeYM89f9FQ1YvhTBNFu4AblrNJ+exF3oCLOAhCI+0oxaPK8wdh/P6RLNunVaxHV"
    "4P0M7Z9MkREbdHvJ2aTRxlIvjF4LpLbLq8JvYIuE7LpZREf3xQYp4l1+v/GQSlPLEf1JpkZmE3EoDNKdp4SM6SXU1fIuDBTv"
    "nv556zZzE1/hP9879J0bt+BFhINgG++fEDZPeXIEG7jcSQkBE77XlnpdBhu7m0CYnw5uPuEq8CHefxbEjqu/bZCxcpigXWdv"
    "q0FeTOlo9ZxsLvnRtFguM3FtnKJSd2lrC8SrLC78Ea2zlu0TmiPoTUW4XFJEVmf99Osc2hO+KKYZjoNxxEU7BM36UhRNKpc9"
    "N2GUhmMy4yXHOZxmy681QCMeDK2PpoEgqicVUyfpbKwYfO+tE5LQijmarl/QlqmXtOXKISC+PdZzDie87Ull0Qg5z3KVVXx4"
    "J1EOzniP2WNu2SgxXH81JV8JZzAr8hgK2aocwyQfALQ7BopmiuD6MEwYTQlB1jknucdUFFZ2SAFkfRFCcxxGhHuRzJEM0JRt"
    "itUIynXJbHsg+iJtQGLx/syhPVqxEyb/DNgc7CG+nkytGEGxv1STTzHK6IUAK0AXo7m6QrBZBA8i39ypAUjdBeVs3yphUdc8"
    "EUXB48iXlw8iILssaipwIO1oqxy7Pyk1175MdseKVaCI/zdSD7rlJ6twZRnFJ908yZz225B2TWXFyYM/4DZtEikQ1HDNos9F"
    "GbXjFPQ5lG3+yOXgakKWHFm9m/nQvxpwso3KnHcLvDHm1WSRFDEu+/5y82roWcTnKwbCU4QA3DM9OB6CTrMsezurN/rSexOE"
    "bA1syPkByOVehJjUaRB/HTkmOQs6m+La3BcMgThQA6CIyaQi25nndhN5RbGLVc5dHp/wbMfITDMfGEBW+Wjs0aEmA4QT0OQu"
    "2SXbFCnxGcaD/Lxb5JhAiidm85kGD3AbrPjK5nfUX+r/q42lLxOdKf99ZQmJ//U6pnMXbvCT+UM8wlWrVXaVGHlD5XzgZBFU"
    "D2FI79U7QoLR9WzwAQ5Y3jEfEMGb9ER9wAN6kehWuNkvhJgEk/YpLLVLPA+kBdu83yjg3RsHVhL0S9FAtStH1CSA0/YobmPf"
    "drMAigsWwGANjD04sIhhcm13CDeGjUe7YR9PO/CDMzqAG6AR+giAWwbry+WN8ESiSUjPJ8f8kJ0Skw0Sm3A0poBRYrugxBJF"
    "Q6oJZhz6qHcAZebFiPyJs2BBVnE+9Nbsce5jeZg8Ih7u3c1OxtTenviFO5W2VhIA2bD6MZxd49yOPVKXEOxzpdgXkHYSrXCu"
    "DIDrIXbkjchjx0rHG1gDrjF+AB/SIRDQY6V1vRk09vTarVRTEgoN3jxmFX/b9JV4Qx8PqCpYQ2eDRDAWqLC/mBD96PMrh2BS"
    "bh8md/DQ4D0O0TowaJEcxW2jPwSpiDm7agim3dQIn1sb68LHgzfnWgdvO7zZojxSPewydFlKzbpCCPqZzpsB9ymc8frj3bvL"
    "mu/YpJ/kD+JD6gwcXRH8WBrHSDNKkRhKj0frFPtQvX/TublPk49UjHp9t44eUIC6bIC72LH/5fpPaTY6htNrYsmE/Thsr+1e"
    "wUI4Sx55fslp5G7N8dOAbZbIXBG6q0g3gOw+gd3bjfx5cBUpFFoP+qxRJRwZwZ34KN1VES2wjOlw9rRjiPF5E1Y1J54TnCVL"
    "BYJIbNWr4yJoeEy0z6VrqofXdKn+VQNQ8NylV3hpedd6PXN9bs2sy1j2RKtjqm3SIlhweRGETq5xGKodgsNXFMHknr0R2cTl"
    "rRHsJeZB+oA2B814jz+/30DeXEFFyAfRx8tzWHbH5B3wl1iKbj4A2wlbUZuVBLDWw9KVRvaVA/A+D2HRPgTxCkN8xMMh1lLr"
    "fOlDoFQTuDV50LlyCEaYYwVdLEPagcXaSi+/1YY8OnESUtWG6zwtvnp5CXE0newxDSdid8tBzXSIZL0ut/BqXk00iazIx3yK"
    "VsCZcQqeU/2przwaunoVAVyDjnB3PRnVDo1pIAgNoEn1KdhMH5HamQYPwuoAzm8LecAOM+PP7InEnzyNndAnfsm0Wr0tkyHL"
    "BSWjUPxpHcDfbsKPn0wUQa0GBdEbfM/It5CWopMlWqwZ3NEIatKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0"
    "adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0"
    "adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKkSZMmTZo0adKk6QrS/wMkvbBg"
)
POP_GRID_B64 = (
    "eNrsfSt75LrSdf+YoEFBQUFBjRo1MjIyEhISEhISEhISEhISEjIyatQoKGijjQ560Ye/WiW7751JZk/u1jlP9szk1m0vL60q"
    "Va1aLOY1r6+/bpY380WY1/fB882M53nNa17zmte85jWvec1rXvOa17zmNa95zWte85rXvOY1r3nNa17zmte85jWvec1rXvOa"
    "17zmNa95/dR1N1+Cec1rXvOa17zmNa95zWte85rXvOY1r5+wbj/m197f38/X/o/Xw3wJPtm672Y8z+sb4Xnm53nNa15X6GG+"
    "BPOa17zm9cXWr/kSzOubrdkW8Gj97ZTeLPbmNa95zWtes9aYL8G85jWveX3JNbe9zGte85rXh605nzSvHywtZvjPa17zmte8"
    "5jWvby/TZ8Ezr/nhmNfHrJubm7nmbV7fB8/zVOeZgL8XP88X4RNfwvn+zOvzbXF/jsqbhxnP8/ps/Pznqm7m53nNqm5e85rX"
    "t1p3M6HM6yfHOPOa11dZt3d3M57n9W3W/Wo+NJzXdwHz/f3t7YzneX2TwPC+nU9/5/Wt+Hm+CPOa17zm9bXWzWwoMK95zWte"
    "85rXvOY1r3nNa17zmte85jWvec1rXvOa17zmNa95zWte8/oUSyq1nK/CvL4NnoOe8Tyv74NnrcV/+f6H+RLO63MsrTV9FE7M"
    "l2JeX3/d6sh4FjOe5/Ut8Mz8PK95ff3VCbG+vV0opU4+wUYyy+UcI87rS+HZ6jX9R4UzPMPPcilmPM/rq/Ez8Dzz87y+xWqa"
    "Zr4I8/o+eNaM51sS0fOa13fh59v1atYW8/oei2Ty7e1qjv3m9eXXr1+/xjTGHPvN6xvgGQaiOyivVqv5kszrC6/1en3wt5Wc"
    "8Tyvr7xWanXAyjM/f7/1szJXQPDMyt95SaV+0gmDlHK1XjckO+aypO95g71tfs6tbZSXDyvRKMJzmvH8/dYDGjV0NO0PwbNR"
    "8kGsZn7+tngWnRXauGt45oTtN8Jz0yweHuZmqe+L54dO6HUr5ZVujV/fduLT3d3sUf4tF3Kywknn3Hfn56Ps811ztzDGzPf/"
    "Oy5BcC7u26tnFNd1XbfjZ5vsfO+/wnptsLPsOue/PZ6lkvToWlG1xu3trY0znj//Wi6XtYf55atVbdO0371ER3ndLoQWrDUW"
    "t+vb8z6VeX1CPIulNvrmNZOoWyNWC6HEd8ezt5a2rqZZ3801/V9HDCullVq/Bs9Np1ZS+xDCd4a0sD5bFVWn1mPWDvk7KeWM"
    "mU+8VsI5Hczy5lXftFrJoMOQdPeNL43J3pLGIH5ePHSMZ90uZZjx/KnxrJXUf2CfKaUKMfnvfGrm9vvPyM+tWs4i+pPj+Y+r"
    "IFtpXLTf+PbaFCYbRqCY1AbFzq1sZ9B8z3jJmmBs+L5nDCZEIuiuU9K5SHg2TUvL15Okmac/6TpuwngNnoORivD8bb0KW1+8"
    "bqRT3mXH/Nyado2TJAm15Z2b0fOJ7paUojHGOy+k/JOwjm5qZ72R39VLtpPeB2Uk+NlaVhlt261w0i+90jr0M54/z83qpHVS"
    "+74MTjj3Z6KQ1EZ03Xfl5y64GGzTwYOjteMFWqlWCiGV0yb4Gc+fZglHWkGZWJ6K66T6o4pmYbNP/ttm7LrU5+RqGQfpZvyT"
    "1rrV0glFkbDpuvFf5/XR69cvoYRQzrhSyqrertfr6FyyN+b7ZqDThvG887BbrXTU6zXxs4rRaNrizIznz4HnJaG3tQK9Jkpx"
    "OdK61a/G82P+01jyS6wYk3MHWYyV0sbwaYoykNWk0mY8f4LVtO1yJZYgZWW8Vw7lSGstute1usqc8/e+UGsdiKB3qoJPRYFn"
    "oZTspFPdjKU3VMQvDssao7rlcvnw8NA00hLnWKPWFLab18R161Z9/5NfFUlRUXCxK6hF9UbXmRCcH4bBxxittZ/Q0OAbKPuX"
    "pM3q2wwxgVkeuodGdzgjUEEpV7wzrzi9Xiujvj2eUZIUXdseFdR2zqTk8/DvNqRtcsXJz2bh0HXKCrrZX/fMh7bCl9RvtgZ1"
    "NWETOtLPxDUc6wijpeqcCz69IgG1btv14tsv7WMJRMjMz2Npnda0l/m0GYaQcwo+WPmpEpY5l2AJz867oBYmxvDVyLpBASfn"
    "J+7v75/zlG87uVwtQwhEr2vp5UhCgpRiJ6QfSpl123GKowxDT4Ss9Yow7C06CFUwEYgOxtA/SFJrn+pASeXHPhmCMO0cxM+m"
    "DNF9saqxxkixXivScfft/egpf3ktV63USi4XlZ93IkRIq3QoTzOeT/C8HZ6KCDHbFQkyaZMRQquYiiPtrLXXSyGd+VTbuio5"
    "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"
    "v5eR+30g+jqWiDE5SaTKJxIVFEfV3TXSDpfSFSu5QvhS+RnfisfB08ZJKHKlvO3sq87JtrFKTlEUpOSdcd6KKapqjJDT3kG7"
    "OqYK5Jw+A55jLLnPuR9KiMNj+Y8pl/Xa/MR0+hU8D9HZjivbdyCuh21H/MxDrU73tNVqRbsjn6h0HayJRn4WmO/t05tm7JTW"
    "HaG1qQ8f/WK8zjtTSpKcOgSehd0d09MLii67d7cju7jM5nG7zaX0mxQdGtb+HM8Cj6w4NwyQP3PsRNeFGJR2tG/fH/5rd/Zl"
    "AKdwF2Jo6yypDuWqdRwyvF4q0s91TOHbZWVi9LCn2z18tI/Qi0ybLKtdYWuNbel9oW+360wOmvi5DJ8Cz9v/bVOhF5ui/o/T"
    "lITTzotRpxzcNxl+Ip6lh5mi12ON2dXzpREzZzEHIhbCET0ORnVoxZL0wyhGR1PANFv2rfBcYu+9M4tOdOy3SHqCfiXJJ3C1"
    "Ma2xySmjlPGms8JYvAWDp/ejL3pKaRiGy1J5lHUvb+cj+jBGq5N9dblUP5KfTeqT2r/1I51xzM+XP4GMEixntfYSHXtCBkKz"
    "NC5bEd5UbvgAfjb0e3DqBc0O51OSOoJrVqMmfqYtwnDtX6fHOy5DTuqFUdabBeDpmfnaYRPBLM+1Wx/fi5VRchePd5N18E+t"
    "JDW50Ia8Y+VuLBg9El8nSuwoObc7Jcd5eUmJqEJrLgZ56yIJ34fgtCWiw6hUH1mzB8mnl8zP/LQGs6hHhEGjcLRVLj2vgi4q"
    "qr+M55zSc9E5gsPn+PkY6/Dp2N0SpCi5nPenVpIq5523uzrRJeOTNqtD8XViEHU4g0NN3l7KxJDom4PyxpWS3z7c9igR8XL4"
    "d8CoVLiBmGikHI+zNTe4ugB0CutZdSieBvsbFfS2/ExXSCn9zK+wli6jOso8nxXWHGP9DPmH5bw/cOkU0j4l6zD/ZCn3CmTK"
    "60r4yqISlMngZqRpFUfvRR2dswEtwSRa89vnEMBK2gYjiZ8FV+tPxyh17yUVv1wS4h29YBHQbEBREwkUJUL+wHokurzqYnvl"
    "pM1sDtktD/sj8D3ymbzFmTL55PY4b45nl4N3dRr0SAZ1s1rxNOCJnFXeRpjU7fJfjJsKavpgPAqOSUbb4OObj5xoGgmcKtXh"
    "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"
    "hCNplpoUCbJ4yigrnnpAElwz4BaGCjvS4aX4E4PH3fs7/XdJG5i7VifRMUWos03lt2uy9rhqRkNiUKXeaRJOJKpCLJvkUccu"
    "XuJf8zVW143SjG7vdOK7ApjZkotklFodvlkMu66swmXu4+3pjLAsDVHw0XUPHU6W6WdBDtIel58KqWzL37Zuic1hFK0oEFXN"
    "x4xGHquSrCTBmzZoNIKH/dATzAmysJVBfQOFteBlNAoH54HtwOffZjQ/0jhQZCKVEfqa/g8fEn2YarvIz2slnTp3g5laLcHP"
    "e2l+ZV767ifiD+NfzieRn+gteuwMv6PHzG0LkVPfxonFt1kS/cXVs9V5XU98CW5esQ6sM1RqiA6pQV+3xH+ZNCCiobOQ1BOt"
    "qmb9QT9QZInBUvSzWl4o7MLBcBTcuIUvxLR4r8S6UUep72cGX/5dPAd4JqNkM3jUA25yIqUfke+gu0sght8dXRECNhp76auJ"
    "nh1sRTxczwwnIClKxGAezeoAko1PZKZA6rBQ7uShFezOc/6qVmeVtdgj9/x89Nkd4+MP41+WR2mj8yNEpNAVKatMcQ/mCUBD"
    "RcM17cdS3H7dEjtJe2n0KsLNWRKGUa1LoDzCWdN0tHO2RMDYBhESgjRIXgh2la1Fm/Wa0rV5qHmqMc7huFvaYOHRhjJMua5f"
    "xjf5/uhW3z8074JnbpqKOBOi16XQjT70kWRXUMjOkHhKOCGE84JDfQZhXBE3U6CY+JCYJHTAiEXL+QsdIbMTyqVHBjjkZ0bG"
    "iUHMNb+Y1eq4cr9tVeWE/VN4iZ8Jjae7HH/PUcaDv8Jakn5lS3tM8SFanTa597Wq7Oi7nfu6JXZCuGFTVM1ewOe2vV8z2vQh"
    "GyCyGfmZG2IxgJAPwwm42CQJ69M1HUmiGQPmejsgX7wH6pG8P3LqPDA0qJXCb681HMDpsnfRwJ8cpoWl0FUIxiannIEbBwxn"
    "Uk4oFoTgSACAZVvlPmJKJ9uMYB48Ds9DSZsaG55t8dkSLPdwO1AHu/TDiQ7aUXNbNVuNajSLkMPAZxKBB2icWgEYykf8PD5D"
    "Gi2y0QYKChDBDtkhO9lJeUjlpAj91y0ZtWF4KuOVpBst7u+lkYdsAMDBFqkdn3K6kDLYZqy+a9GiRQFhO4EZhtv0dY3mJMjR"
    "3tmiGKg9jPsXY5PAiOd7nd4Yzxq21eNQd58d+g6scdrDVZao2KeUSW+QmMilwBJ8m5KP6LVLmEWAudpExx13mxCMCRGeuwUC"
    "Gsfl5Gp6ULtPUd8xT55wc5UnuFAnERn9hgrIaXpevTL7Z2F3TnNwladWrQnK+6+uf9IWResUBXgn/YBMR73x7fFEgDq7/avi"
    "uezLJqsPueTqBUCvZu+4qZDvCo6EuYVbqaamRARPValW8US7BOYxA7KWcIzuDvbOQDeoHkbSF+5ZeUWk3XV3d/zcvDk/62SR"
    "YDPAhxmGwaFWgvZhnJXQ5guHO2dD8ege7UHcGb4DyLE7C9sBX+euGUlfRZS9welR2g7RRx5vbtAmbQ/crQmlfBUZrYS8U2VQ"
    "33Bn5WnG7LQnEiaBQhw8D8f4r24Kp61ax09P2yIERocCDrOxw0j6Ibzl7o/QOfut2vVXhDJOBNE3lKaBHnUa0O6aV2ap0GsP"
    "+fngUIrRTgEkyW6iXRYbqGCSpJSVEXs8896JUKjhwTpT5+2Cx/BY0d0d/tNb8rOWKLZHD4Ib/t1YCFySC6nvKegnWZwj+im9"
    "JNIFjJOF7UByxOvZW8fVV7x1eRQWVfyknqjcBysrRRY7Pe5HKeFGCGW7a0kmaQUu67NpM4789s/DzbHm1bCX7K4kQbge0LB5"
    "iLZ8NFgfmcY0vA8fOAk7hWy0+IoE/dApaco2Y0imQMA7TQNa7A9PTuUaXyJ6+3zxYZhUifa+vb9nWUwfSISoUaIsT4NtuoBs"
    "vXSgmteNFHq9vF+/kzMYH6SY7APc5SgYNCL2QywF3vhliDAIRa4C3UmwLkOLpHERgaBFyq44jvVQJ2tqHgDV8s6PZ9bg58XR"
    "4MDp8imnd8rgzOsfY7jppx5+I32LRQ5FHqHzlODHv7e0z2CWzdXkJBp26z3YCcmbm5uRnw+/2iHil/ZL4lnowKOViFpEIIFG"
    "/MzTgPg9Hx4IIi/V7Lcwko6Csbk7ibqn1d3XyHFsBN/PrjnII9EFxCC/xf2avviOVMavX79ubwnK9EC8Q669YwRKkro+w3e5"
    "lgBFjE99GgpJZUIjulz5uDuFoe8zN7xqHYZqoIoqJtPnBJc4YwuGY5toJoxJ7eH6vgPdIW5pQ9jjWa1PRYWBicaen611urHF"
    "mZMa5VMBPv0dub5Lc0OJqJB5MdVrc8I3GwXfLG/OBQ7UOCnA9svhmXWu17L+kfaq2qXSjfxMHLsr2BDoKBpBOvJzqMKDoLsL"
    "52pf/uEdnHC8n8k0nn8RnjEa7a652w3Nrt/9xni2nc1OLzxakYIjzZFR3hop0k/D9pH4NnoOCklEF6tsSNvHDc7yLb/lWv2M"
    "JobqFsf5hLjJ3gRdyZn4AfkS0070dhj5uuzcNCJzvEqHRjgmH3mKWxQ4OVI7Wl6REOd/v+CrQ7E7PXdBTkAev1xTXKCInw/x"
    "TOrqaub6/Azy8+FZLA/OlQBeXOv7plmzKmxR2UyqYMfPFCV07UQgLQfAUMKX/UOn4ZMXrwEeGVDzyM/QGbe3989PgP9r/AwH"
    "udhvUu9AXHHTb0umD1vMo7TOUjRR2EWJwr+QUdUdSDezaHaZgQ1jBwoT4RlKmhoej4F0iKgUi6Yc+JxPgDA8IUzU7C+6COyh"
    "EmnhdjkF4ua4QJP42Tp5bJXzO69WqXV3NFeWiFYrIcYfwtO7xukgLuxcEkb0yjHpjHv+jKXJCTd9Ln7e/1FV77nFPUlZzvrw"
    "uzzIpdFfOttOAq9+84N4OBrifqjMH178QhAH3q7vV2+K511q2MVhyClvB0xrVrHAw73vn556p3yBUO4j+kVIYpCogrdddX5x"
    "sJXxdupYJVGibeRSJuLzbGtgSHhG5l6lGHaka6AIBDdviZCzPQz4kIwnqNNjTb+ggww7zO9AnbdHqmSKmC9kgeq2Cg3ubLcb"
    "jtUatoQ9ENI7OjfBLA6j/l2hCP0SegyuxqWflJ8PCXQXq038HKOq+yE9q8vlDgqccOY3OooD/JBJLxxvXvjMSw+vV2/Oz7Aa"
    "SLaign1hcz/8O2Bcu0HbDFHzsB1QUIR2KWiIBCdntIvCSBRehi4gSKw4Yv/oEoFneIZi2vvYiscW7xRQRdIrtVxl4meP0284"
    "UdkdPOlKMp6dINlFMWcHJazpMZnOmlEzwI2dOxkx8fOF4uSOM8go2nMTP+NxoGUvpirquJdL6oJ/SfMm5XZvqCgPCVSMDTe7"
    "7YwCZb2ennu1m322fzRr8MZfP/HzzcPNybNyu76M54s5qePH4W/j2eP4pIb1gEt+7IdhE2G+IvN2O0Q++CtxiCQpTO4LtETA"
    "UTBQEuH4y4PW6pkG0BRwSEh0x5YM9ONDyoF7TLTxSqCon8QLlyaNB1XeqynVIL1cI7zWzVh8e4eDJ4Mk2YIHxdoFH14hrkSw"
    "x/ORmX8n5F3gZ/QetIujMqg6G66VF5OE3bXU4TP3qN7c5cPfuCV/jbxYuB7z8w7PauwQxMRisZ7eN6byiWPpVPl5nzC+OQIk"
    "ZMjienHR0bM/hY/HsfbfxrMheQDzRJYBoQzDFt4abCaEQX0hoYE3oV3MYxJW5oSc9y7BZARWd5VZK1jw0flIjwfmoBAhcsFH"
    "nxzOy1tF3waDVvoGkupBmvEx4r5BT5QvSDSvLenzCTIw5AGl4lI0TYdSAjXOUSKhEgI0y5qPplqrrpiYYMxFOOHhkeg7dYpc"
    "PBaXhr1dDjgvEaH5G82yf2dyA3IKZ/nJdhTIZjcByI4Eze97V77VVPStd2rkeS1zWVsfPfvs+wi58Zb8TNrXatER/zKytk+E"
    "Z+/3ZvYwpLDwSobVEVr1xmYDVxI8lWC2XyCNXYKPo8mYrWisgW0wKekINz+gnzO8LdJuKmLAEonzMM2s85lbtIvHxWw64/ae"
    "LZp0RTde00Z38O/RYHPWJXCyIUIJ0TM/u4tm43Bu8u5KUuLgOGy8+CSYnwHtyanNxZtr/kaz7N85PyN+pvdWH88qIPZlWxPS"
    "6CKKkZ/5Mu/TqTX9NP7ntwj89VyM97D7+Tc39+u3rauD9BXrmCPKr0gtYxbhodMXYREtr1vUtRqLWRHccARvGBwNy+BCsRQQ"
    "Ope2CZ4jjlUt6JbARHrb7mRAS8yNMhXMRAI/a280j9TyI7WzFXVzwHBEz+34YHP9gGhRKlAdSbuxUZcHYdDtwRN0PndZXjaf"
    "OvzCKejD5rgrhrzKz7+bGPeJ+Lm+t447U6uAOLdjpYu4HMXyUenQum33/Hzz+wDuMj+f6ZCbh/s3r3sWqCbBnBieBNX351MV"
    "NOxlUSDKvqI15ooDrESl1pK7lLyKCe2E3PiPNmKP2g92GUDlS62xlbHgUA8CANMrnEfpKT0uMXDezhhvom4OojCYzolOIE1a"
    "6+JsrY5GlbRBS7xAnbLjM3NoiMNbIqd16T0ffuEhP18QFSfZ/3ftsrj/dbOTwa9dt7e1QIb4eaq2uPQmUFZUex3qMz4+Skfg"
    "foHivXxGchQnAtxvGgtOb04ZZ0Lx2iiNSYvx9CFGboIgKzHeeJpIsIgFDuW6WkG53uEMzlqukrbF8RhkW0g6k/LunSAmRucZ"
    "yB191J5Hdlqi/EifQAc5bQ4kqon0UdK2m2ZisjU4lUWORCo0caK+lIEXEyxcVchsFjjeoEPaJQ6XV0cmri+2s13Eaj3b/Zj1"
    "awU8N3+kOG/XuwqB43eL7NG+hH+5XB5hfZQ66wb19sslh98VhTvIXgLl5at0xM+36/fpSFkudUQNUkbTakjn7scqwBrRSxvT"
    "3vKFm2VJbJBegJ0MixCSZxAP9BkPW1zr87AZMmlqQiuFHUiBANlGocUlYNQKe0mlwPxss6+TtP9/e9eq4CrPRedhUFVVVSgU"
    "qgpVhaqKQqFQKBQKVYWqGjVq1Kh5hv9x/uxcIIGEJFzac863tzpnplNasrJYe2dfxopguoNYAhfl53vLxtXA4555zf1vX9GL"
    "9jz7bYhJ5DyOByUxBnK2u3qDPvZkntcYQ87lEifncESf0zw3RWIgW5He7cxSoCqlDkNfSu5MjLF7MKRdKPG6kLv0qgqrIS3n"
    "9/n9sEnsnvJz9fn71YoTPRkHbliH64qLEKjUotwLo+yYr9dCmh6Fc8MqtVjPZyp4IXz984DSge+ubJpKvh804YWGYFBVwPg5"
    "Zx0ehLylXHwX/U44P/f9HfrX0s/FugFCSgLIkoZ11xeOT6RVR0UsnUCsmCnstqAlglAdiwS03WB9uqyIcVmOK0X/BVVQmLY5"
    "+8KCnzn7LvLzOj1yoN3Kvn9+WTp5kw6CDiW0l6FSoRsaGQHuqoYF+6qaZx4BrilsKKBaik/on1s1X5BV2n79sjkW0HaI/UUN"
    "xVmfPBcfMAmNPGCSHcMiQCuvWQ0bu6NGqHXfHb0ccw470PRUluSsFbV0fCJWMcubSAwLx092TcciC9MrglRHDIVMu6ZJJ6cQ"
    "CPG9ajmuFLdC3XCmiLumDraj8RU5dfo9qMoCiNTonROYSHGHg2BIKxoLKEtInytZJcqQ/sBbCkGTzq+ueVB1QZUxFSqUoZ8M"
    "z+1Ddp2h+vanb9nBCpSDVzA0ruXN4NuuJ4KfF6QACPGugr1wl/ysozKSNYp3Jf3ZyM/Rx8fidKG38rN+yOLunzDPyV02Az+f"
    "4nhXdfB6fr5BhaktegoKG2azQQU368Elcg3rB4ExbgzPhMeTRcuGGhrIQOVICQ0Lvvu+HJX3EA+mcr3kAp1isutAwcsS8I54"
    "SQFnuIGXF2tniGpQw5efvYKwh4Y6hlCuG623myySP61NlTiF5QzpSXbvdzw4XZaZKXpK5TOhNHvvvqkXV/a8c4B4RBERPivv"
    "dSlO/xuYDVFU0ASbpRtBQ5mvx4Mf6/G8+7LNxTvDbKziwf1C4POW45nASeJyhZkByMbXl+NGUnPjfEZ/rYDxgZA/S2i6+fmc"
    "ycfZBJaWp4Yh3D3ZCC5smpLs3hkYEl9X6fs7RDEgZYXdHSqH6xJKqfumJsojCnoHUP+vL3m2PpOs0CmLDWGj/310j0b2+mL3"
    "GRq3wuBnUjOsFc+fB4v7UR4XHe64dllsfGgQIPrrBQMrnOvkZ1f84x0RO2aghQMYM0mImZ9HVa/5dMpxpMXXc8nfP5Gf6de9"
    "T5wkAom/wM/QUZxQBq7aHOZGdEQpL82puO6g7RN0OGA1KGMeJ5SqQOM6eX9lXVT7Tf3LAjqeQ6J/37ddzTrmFir5buPnBQa2"
    "Hr/dWzeencr4umdx3OV6ASCnJAVocrQ5P4EVfeNfakckyie2HJ28H5srRfQEz7IwA07/HhBgrnJKzzDJ6nfEMw8XU3Q+KwI9"
    "7CiYJStCIlvz9ZhBj/FzAWWywLMtSw4pmrbZcXrdQiWJNT3Ch58nkQv4ppHfu6/FM+fnEW3sE5iiF4kJfWYoqjwsAsPJ2lic"
    "8XMPh5pvzgrXNv8Qvi2bT5hyBIsHPNxD31AGfsbGz+cTJivDmeDX/36gnZmMFMAbNK0l5WGoi6d4pkAi9bMv/Zy8jbc4hEFn"
    "yzFhx7qvrfwcrT9DSC78L/WrCX6GVgNpAWeHZrRo29IuFYajkwNab425fV5VO9fDCr41+qk/a3E/x1mtBIYVtk3FI7g1y0n6"
    "6VsYzFGxOW8qP/vFI/irCYws/Bjl89yapt0w2e6SX8xrvuRgRWmRLWY114vN+tef8V74Xxrj2FmVUaLIKJ6vN1OfSU022aUC"
    "q36i28Zj05n08Z78TD/KQZkdGiFAL9Qb/ziFKARkGZtsKg/AoGwaiucngL0lRWPPlRwEdFfZEElKuQwD6MW2qFi4A8r42m4D"
    "nrW8HmXN50cratfYjCSBsVsVzwIqoWsVx8nIz5f0Mluj5rMlgGe5PFpUb+kzKR4iq37y23AJST6ONKj2ekk4NJMEULTV0OWw"
    "GRr4ga5g6XQlNBPtH81MqUzCEaQSFVKGyOB8GYRsqXgKa0EJnPHzHt98kZ9VhIdS0y56kYkEuQH5s1vDXdzw0S4UB4G8podJ"
    "6F3ww7PrJqzV3cMb75p5Z9/QVDuk05fk+Yhn+o+GxUDKooOCqsHh+2zNOkNGPuqlSavyRQo/Q5KGXWxEKzFukRo3eOw4LZr9"
    "w1svuvmZJQBddJIflzweyg5MyUGOAKC68OKkO9m6UZmnmswfTO8hfnucqugM3cVZnENzGsu+hBZ1ZJiQ0j4cMzMW897niZ7F"
    "Y9eR0BINtrM2dbdZw2OTXwifZjd/Ppm+kxJLo3gXwASQr+e2kIA73ah2lE4/gq/jMCX+fUh6iZ95Z7kBfowkYSSuTKwfiBRO"
    "4gYgbglR8CZ/M8berSElxaH0OBk/GwCr7rasyj6MxKP/Qu9g4V6e+SN8mrjPIxPjT3XMpFlqAPqBRreXv3t7PmcHT0xZ+/4c"
    "60NiB0cs9LkmvO/+oAIA08N/5oNY/VnaQpq7zUnLykzbbqwP2816n/QfKEtq5mdv+tWftBQt0/pVHpmAsIyO5LOiaxja5a+P"
    "OfVQNt6En7XrTfenO8MwX9057QZFeeP7B0dfeIcAjZFhPuCjlMNk5g904f85iv/1/CfZ792Q+vbx4WoYPN8ath08/Tn0yRwd"
    "QMc67JaVPlkECk+Nn+XuOMUxxXN6/rhMLpym8BTT9sAxGRP2BkhaaHv6Mjd/BuTQzBiPAmd8/5AWTcoNnx6LlHysN6Quz6BG"
    "yZsIfq7hxNsLhK6hPcs7buZg+ucgR0v87OdChq1Hnl8d3pY8ZWTxiCg6Jxf5YBA7KmY+xbgHkgV+Fr9Ytxft7LfIz27byM/q"
    "pbNwpyUtZ5J4QLhhdsCI/vrZuQYqCtLf5Er587NPyGKJG5x4dj73b3V5Xf67eOBnGY8Y+HlQPIX34ZIg0vPtVRVPezjDJ9cm"
    "o3CRW2JFUMkANiL6GfJsenMEAYAm+NkuMKtH5QH3nR2D1dxwc6lmZzGG4OfpLaV6Afg2WWbS2e+WeRHecRM/76mqAryL28kF"
    "RQpi2a12NRNO/Tumnh0iefoIteHZ6jtKiW4+RQ8ubcr37OBs+lK+ftmEVU5pGotDeXHqwZZJvJsosg6+1rxL0g7m7XnapK2L"
    "hBb5Wdw3hZ/XR/Ym0OX8fKdaROct0+e18zMnYC0KrjVvllHBvtyDn81+yMqUmLA/S5YeeQBioYeFymAOBWP701gSm7ifBXGc"
    "DBGRle07vATMen7mJLTys+2YsmdJNCJtMeZOAxTX1INq/GzKSYKLG4ITodcxb+pNaZ675IdNku+pOhj5+XS9aDG70yJTxnni"
    "E5JeH9/bHBnky3bIsyPI1CCHggsqpOuhtoVAZ7oic62XVWGwaInKz7DJOUdrYUd+Y6qd1LMJkvTCfkjdeWATE7ra4UVYIWDs"
    "N3Hn7RVRhzw7wvBcwMpxHObqZBxFbpDq8TBlfCqpMJFZvQg8Tw9O4OiBa2gt7LizNxgZ1d+1vK7cDO6PZ/XPGJQ3eW9eoU9P"
    "ll182RZIrnUW9zRY33vBlK5VjENHL7L0PJVLtcDP0+898PNqlDopLlrPz1Z4L+ou6/Hx9kBEmmWx+/noh7ElsZyk+Xo8Z+T9"
    "sxxhqe5tQSzLzDHeOgLOp90maMCO8AT5eNHDsx2yQW2t4+djPDavu24ISAA/22g4Iek6PEdrIlMHGQXRdahd1VmaK4j22YZ4"
    "PmtlooiJeLZcPr1grJJE8WyI7GZZNMuhczj5BpGwlp+ZrLDQ8CbJsMGL3psKrqVM4NSiXxkp7x/Oxiz2PRtM3AH8vFYqrliy"
    "OZttoCKO5FkOnRK8To7HwwGe26YYye7NSoczu5yQm7Js+SZHfy8OdaerRr5PaeuRQFAU1MjPfrqHIznKsuv6yx+PhxV43hJd"
    "OVCqqcVJ4Y/V6OOIDkSuLvpB/Jymxnv3qnGDQmn4BVr+ADy8hJ8PtD0SzjaveSg/L7LbZFdauOzFjSWuL5rh/rINijYlzg0o"
    "WCTXidj9A7jsj1+KAB8jTjLE82pWsxzchfAzmtNBDMmoT+4p4nnbUzoKESt4s73wrKVehPBzkiX/+L0J77YSH3fJaO9P+1/g"
    "5xDxfHndOcBfYi8fXvBftx2PouIrrt0B/IwWhOfrfnjOcO3+Zm2E/KwbBosQYGhoaK8wD65FeYH2D9j7S0/Q0HbE8w3xfJBh"
    "OAT5+V+CB4ar0Zbgcf/b8Iz8jIbwQENDQ0NDQ0NDQ0NDQ0ND22bHlQxi+g7aG/CcIO7QkJ/R0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ"
    "0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ/k6T2ZP/B376G38="
)

# --- embedded background picture (JPEG, base64). Drawn behind the pages under a white veil;
# --- no image file is needed next to this script.
WALLPAPER_B64 = (
    "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"
    "JZcqELES2+fQ68unFl1nUu55s2Euoc2W89bHh184GtNG7OpVhXJS0aJEoBijTlpIhcppywxC51GtY0miECGqI05bHnvmqQMI"
    "o0osrlqw5jGXOd1RazoCBiJKlymorGIqDesal05Y24U240acNiQISxAwGojUVbcJuyyIC7cauVzJqAiytmJYhXpy6J05dOSb"
    "3z6liyUIFqtas3OMabc6C2jC2YlaYmqcgIUunKKKVBOU0lDELljo40miECGqI05bHGsLECkaSs05UaCy4XFGdVQ0FEMQwkjU"
    "lYlEQu9Y1lpymnKmnGjTmTQVRC0ROY1Zq04TbhN2Y0Aa3z0mrKjAllytmFoJddOXROnPeE6JlIq1wg9cdbkx050YBXJlpyUr"
    "STFQEMSsQ6yi5USicpqGKIdY1G3LZohAiaojTlpxrAkKuVNOVNOWkpDGuc0FS1UaLIxDENWjCSVlRLVGnLGojTlNOVNOE0QI"
    "VRAxDErEm3CbswwGt8t2asqaCAskQ1FQ9eXRNxpmyCtZp0dkdHO4OTi7sBNoMszZJkclLRDUVQudDDZUQwqpJRK6xqTbls0Q"
    "BEtEunLY41kiJdOWlFNRJqCw57551RTUikUVCtVlUKVMRRDELljURpzRpy2acxqIoKSBIViNWY05U05jQQ657TUVmgizCkUt"
    "CuunPozvOsMxatF6JbMXDx1xbsWZupWZsiwIUqUVRVFUMIo2VESS6hiiLWU250ykAQtEunKjlyUSrlNOWzTlRy5DGsZ0xKwo"
    "VLVFUjDTURRVFEMIxRqI1FWnKMKUREKkDEMIuWlyohK757TVlsSCLMtEq51Jrty6XIOklLHWayDlKc3M3UrKWOAWolqlqiqq"
    "qKqFy2ahSEWqhqKIXLG3OrEgCJaI05aiCoNQmnLZqJHLkMpnVErREkVQ1WSNVBVFQJUskNQxJqI1EaipiIgSiiGg1EaiGIdY"
    "1Zpy2JBZSWJFuqKtwaMWNjc04cSvKFhVNGLHMNVErEJRVVVFUJQpJqEqIoRhIqFymtZbEgBzKxC5RylURpymnKilURGSpqqi"
    "oGIaipsqiqqiioViGIaiSGFGI1FWiBIKoolYhiTUQxDrGxRshAGLV0ZurnWEzhXMzWjLGuULSFkFololqiqKoqiqKoqiRFJK"
    "gYhhIokY1rLY5QBJSoYSEKqmE05U0QREZqmqoqiqJIUrGIYiiWqKqKqqoYiSFKmqRoqqCpaIYhhiSsYS1jYo2VKGrSPTDc65"
    "ksGZdUrGshXM1zqailYiqKoqqqiihiGIaiRphSEKqWqKgXKmtZUc6zQOZWJWpIRaoUUUrNEFlzLQy0QxDCVQ1JVVFLQwVFUN"
    "AxVJQxUpCkjUQhCLVFUVQwlMlqbFqySTVnRoinBSm2LSRnmZIJqoViGoKiqKoqiqKoqiqJEUrHKRVLVFRCimnLYjkspLRWqR"
    "CDCWsqahsSIsazLVLVFUSQ1DEiUtQVRVFUVRVFUVQxUpGokSgqWGBopUFaNMzOYQlY3Y7yJGtS40hWesp59cyyixS1RVDRVU"
    "VRVFUVRVFUVRJGoUhCiVqiKpc6RRSEM1KVStRCEkKNjUiQoJLVRVFUVVNRVFEVRVFUVUVVVRVFENRIjDZVBMDIKhqLGJEJaE"
    "nfSXl067TlrdLjDxs1zPQPLfnlCKilqiqKoSiqKoqiqKoqiqKgYRRQEKpZIqi1lTSNkOQElqlkSKKoUUaqiIBlGihihKqqqK"
    "oqqhiqKoqimCqKqqoqSpSpKahZBoSBHZzPR0l8nX1UvDrsg07TLeeunn5msuX0TRqxlz5axuRUpItUUwVCIVRVVVFUVRVFVF"
    "VVSSKFQSLTQSCjYopZ0LkQqpZEhEqSapqAQKpaoqgaKoqiqKoqiqKoqhtSZmCYJTNqBaypKUy7TOmi2al0CaYldKZ2crnvx4"
    "43mwls6741nTSnk7cNZsbwpMEwTBMpMhaAmUmCZCYzagNRm1GbUExTUGgJoGiGJkmbDO8mTRKTBajNoBkFkLRRneZc2ozajN"
    "qCYJgmCYJjNqXNqM2ozak1bkxdAxbjF0LM2kxbjNpM2ozbjGtVmtY6ZtrRF05cq788NhazrOc7Zee7U1155o28sVi0mM9cmL"
    "cuLcYtxi3GLcYtxi3GLcYtxi3GLcYtxi3GLdWLdGHUmTcYtxi3GLcZdJl02czrmOZ0F5ulcW5MW4w6TDuMW45nQMW5cW4wdI"
    "xbjFuMW4xbjB0jFuMW4xbjB0j2XWzni9Y5XWOV1jldY5XYs5XVOT1jk9FOV1jm6jBuObvVYd0nM6VvM6BzuqcroRyOovO6S8"
    "89Y5XWOT1jldY5XWOV1jldY5XWOV1jldY5XWOV1TjdY5XWOV1jjdY53WOR2E5XWXldZOV1l5u5BoM7DmdSud0lxbkxbpcWqw"
    "tQWqMHQMW5ed0jndKud0o53Rs5XWOV1jndKXF0jndI53WOV1gqyoSipihqJKmA1ZjViNmI2ZjdlNuZNBVoCGJdWREBWzLqIb"
    "MasxqzGrMasxqzGrMasxqzGrMashuxG7EbsRuxGrMasNashuxGnEasRuxG7CmzMaCGyLuxG7EbsIuZNWY05jQQxDAunNGokX"
    "MaiGIUhqJIYjpasTK1ZmCpYgQhgGAYBhGGtWY3ZbNGYYpVzk0ZDVkl04a0ANmVs0as1aCGzGnMaANWY1ZjVmrVmNWY1ZhgNQ"
    "GrMacJoIYBiGEooYjUVmiiEKiViFy1VElC5jTmTUNVUFQ2aXURqI1Zk3ZjdhNOI3ZjpYpNmI2ZDViNWZdGY1ZjRRVVVDCTSM"
    "RVFWRAVClqhYsiJWIqiqKKqokiiGIYiSEgaiiGIYhiFEkahIhBqKQJiRGpKYybDMykxUmbQExVCkKKVQGozJLRDCMQxC5jVl"
    "NlRFFUVRDAzRKEwTBWkGUJgmCcgMoIoaA1akDWTMykwTBIQwVVVBUVRVFUVRVEMVQNA0TVTUQwTA0VISFUKI0oGoyaDNoUZK"
    "lMmxczQNVIjUjURqMHQOdolKhhiqWiOkyBqCYJTKpl1GVgNASpTWEwKBIAgDSgi1aLUs886GiYJgkCoKiEEagoqiqKohiqKo"
    "qiqKoaaqhqCqKoaQmCaDQjUiigalxaDMy1JUpk3miSUaqRGEYUqQNRjPQjnbypUrEn//xAAnEAACAQMEAwEBAAIDAAAAAAAA"
    "AREQE1ACEiAwIUBgMUEDIjJwoP/aAAgBAQABBQLHPseEfqvoXB495B+q+hVeQeQeAeQeQeAeQeQfuKryLyD9R9byDyL9R9TH"
    "kHkX6j5qryLyL9tVeReRftqjHkXkX6b6nknkX6b5qryTyL9N81V5J5F+0qPIqjyL9lVeTfW8M/SfNVeTfW8w+ao8kqPIv0nz"
    "VHzWNfW+C4P3n6T5KrybyT9hUeUfpv336L5qjyj6UMfQ/ffo6uaGPKPp/nF1eAfo6uSo8q+lj4Lg8A/RfJUeVfQsU/XVHk1R"
    "9H84Lg8C+9j5Kjyz6GPMMfJUeUVH2Lg8E+9mrkssqPmx8P5V5J83lVR8lxXB4N+qqPKofP8Aj6Hg33MfJZdD5voY8ix83lkP"
    "l/Oh4R9zHnnyY+byj4rLqmriul5R5xU1cnzeTY86qPguL4aso86qauL5IeVedVHVcXRU1c5xzyC7VR/vSh1Swr7nkF2rguao"
    "/s10PpnIvPKq5rlOSeeXN0VP5lnnlRc1TU8u88uhKmp/armhIbo/tUIfRqY8u8+vyiVVVvMPPKqXBujf30jfKfsUuX4h/bpc"
    "G6/rb4t/Z/io6z9yhvqn7VvpmPuW6KiGN/bKs8EjU/t1wiukb+6jh+n4an9ukQRVs/T8NT+1Wli0kcGxs/RKBsf2MC0MWhEc"
    "W4Hqp+iUUbn6/Yy2LSiDxxfg1a6pSJQPwa/H1UG1m0hHg818nisH4PWN1Sk/D8S8J+fqZPNPFPNfJ4PIkNpD18Vpohf7v/Lq"
    "l/W+a+TxTckPU3yWmn/J6nJq1Rp+siqIPCNz6n5+Cj045RW2y2y2y2y2y2y2y0y0y2y2y2y2y2y2y2y2y2y2y2y2zYzYzYzY"
    "bC2y2y2y2y2zYy2y2y2y2y2y2y2y2y2zYbC2W2W2W2W2W2W2W2W2W2W2Wy2y2y2y2y0y0y0y0y0y0y0y2y2y2y2y2bC2W2W2"
    "WzYbDYbDYWy2y2y2y2y2zYbDYbDYbC2y2zYzYbDYbDYy2y2y2y2y2zYzYbDYbDYbDYbDYbDYbC2y2y2y2y2y2y2y2y2ySSSS"
    "SSSSSSSSaSSSSSSSSSSTSSSSSSSaSSSSSSSSSSSSSSSSSSSSSTSSSSSSSSSSSSSaySSSSSSSSSSSSSSTWSSSSSSSSSSSSSSS"
    "SSSSSSSSeMkkkkkkkkk/+CV/9uf/xAAdEQACAgMBAQEAAAAAAAAAAAABEQAgEEBQYHCA/9oACAEDAQE/Af16N4/ID6QeYGTB"
    "8hMG4YO4OMNob44I3xUwdM2MEPeNTrDimhOANsbJscvAHVNjQCi65NF23hVXYeFVd5e7UcA7CisB3CY+y8OOOOjo44/jK/CH"
    "/8QAHxEAAgEDBQEAAAAAAAAAAAAAAREAIVBgECAwQIBw/9oACAECAQE/AeucAPjYcJwA4AcAOAHyWs+V/XnhfO19AehN5cex"
    "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"
    "RWkKwpSlKKK5ZfLK5ZXLK5ZXJXLK58GlKUpS4WLmly2UpdFKUuKXFLopcUpcUuaUpSlKUpSlKUpSlKUpS4uKUpSlxSlKXYuz"
    "fIpS61i5pc0pdNKXNKUpSlKUpSlKUpSlKUpSlKUpSlKUpSlKUpSlLopSl0UpSl3ruQhCEIQn4tKUpSlLilKUpSlKUpS67opf"
    "xbv0pSlKUpSlKUpSlKXCKXFKUpSlKUpRMpSlLuXauq4pfyrppSlKUpSlKUpSlKUpSl8Gl1L/ABalKUpSlKUpSlKUuLsX/H5u"
    "XN8Kb6w/2J48GvNhN9CQ/wDApvwaJ4cJqhN+CX+DJvwg1uwhCE1Qm/BISGP9uE2ITfhBrV//2gAMAwEAAgADAAAAEHjscBJx"
    "rJJc28n4EBCcDMsget5t9m+LcSUd880cbp3FkqBo1FMizfUd8Z68RbWfRADZZj2HceaFnuzhUTCsDX5uuzkyh2sCkwvPBHp3"
    "cG/76rOO1CA7d9xa7lcv81cZxAzLWIs/adW6y+HpnOdhPIqlhCQDYL+BLEYh4zjGJpMZ6M5AKL3ayWNaREtDf81lL8L+mycm"
    "nV2XHGHpwcM53c2q6cp5mVn/AOcU83lFPI2bpnUztxM0sVifoMeHqAVme7ITBEFhJeelVFHfGzLODqB1EzL7oP4dXHHzIHFH"
    "G3BkeaFXRacMerBeIu/K7L79HRsetKNO2ih6jI6X2OlJiV+gosdQO7GddlskFHAlA/UeaFUJ+MmXzu1ofKqnOMRJSnN1i9tm"
    "9s+xcmOiPD72cpIbeLi14NxIN5f/AGanb1OKl7Yy7PScIP1Ch8YaV9x1csXOhhIYkeijfpT1x72KOwgDVMqg0p38WFFK02nu"
    "Y2NGnzZPbOv3LPksNlRRbPZkpFyIlS33vDfFimAmMkvzTPOJ8o9BZGKooYuJ4CYNRmYYgOe2PPuEQmkvoY2/vM0RJESBerBb"
    "WeCUJ5DV/X1GrTRB9kgFfZgZJ37eh8RS2pOOZLFwQMPtxv1bFk0dmMQv8OXOtoFJD8ArppTXjS/AgRFNRIOV/EUeOT4wnnr+"
    "2Ydr2IExnIuHZjlSBgB5vIkDSHtQhtUUq/CvlGOaOF5FBH/+AqGWqd7989DB7TnMZyUuLSnyY/ogdKMT44qlFBU/XPMvEOC9"
    "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"
    "syIiDhERERbkRERFmW5HThwiLM7kRERERERERFnDhbluRFuR3M4WZbHk4RERERZwiLIiLYiIjmZwiI6RHCIs6eCzIiOZkRER"
    "ERERHNzhHCzOEWZHC3hEczI7sdzIsyIiI5mWZEc3IiIiLMizLM6RZC3IiIiI4czIjmZ43I6R3MjyRERwiLMjhEW5EdIsyLMP"
    "GZzeERHCIiI6WZHdzyczh4OkRERw4d3hbEWZwsyI5kLeZHDwREREdO7HjM5meDhFnCIiOFmcItyItiIiI4NnGxEcOEdI5nSO"
    "HN85FnSIjpERwiOHTuxZlmRZkWZZhzYjmc3OkcOERHCLebERZkREW5w+EiIiIiO7nCzIsyzIt04R04RFsREREcLO77yOHjOk"
    "RHDwRERHCOFmRbvfrweiOEc3PW+SPJwiIjweMyPREWZHN3h7Lcj3lnki2I5mWZHrenyERzOEWZbvCzPhIjpHc8ZndzpHsiPR"
    "6zIjhFmRwW7zMjwRER6I4R5yLbeHg9HSI9EWd3IiI4/m2IPnIjycOb8ZwiOERbkcIiyOEWZPN/yzCJ/RObHveEdzIjhHjPgO"
    "5HWZbvfuC3ekRERHjfGWW9zpHN6REeCPRHN6cLMiPO/nTL/no8keCO5lueDzucIjpHSPZEREWZ0vq3ebv8gzh+iRZbERw4c3"
    "I4dPBERHDh4IjmzNszIPxZn93h+plvDhHd4cOEeT4CO7uZbi2rZkNhgsx1tzweSI8HTp8W+iPRwiI8fm1iItdszn3zX+WKzI"
    "iI6RERERER0iPgI8ER5PRERERwLLmc6ts/uGdOnkiIiIiIiI4REREcIiIiIiOESnZ2dnZ2dmOzs7OzvBjs7OzGOzs7Ozs7Oz"
    "s7OzvB2dnZ2dnZ2dnZjHZ2dnZ2/N+b8zs7Ozs7Ozs7OzGOzszM8ZmZmZ4zMz18Mz8LMzMz8DMzMzMzMzMzMzMzM+mZ4zMzMz"
    "x4z6fDMzxmZmZ8MzMzM8ZmZnwz1mZ4zMzMzPWZmZmfDMzMzMzMzPhmZmfgZmZmeMzPWZmyfDMzPlnjPHjPpmZ6zPGZmZmZmZ"
    "mZmZmZnjMzMzMzPHjMzM8ZmZmZmZmZn1/8QAKRABAQEAAgEEAgICAgMBAAAAAQARECExIEFRYXGRgfEwobHhQMHR8P/aAAgB"
    "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"
    "lb1L3LbbLLLLLbLLD3KWObLLsvBfmHRPNZze10D4tBzPj6jtvBe1Lu227tti2I40ltth4ERbbHAYZZZl6h6veG8JnlttjzHJ"
    "e8ynZztsQ6JYT7523ueThylKUoYb+ZZbZZerbbe7bYZQww22yww9S7tttt6llllllth7l4n1PZss9S8E8AfD/fvPvPiXd5jz"
    "P4n/AIcGRPXzLfzwPBHiPMQe8ssv3fzwREQ8DDwGGWZeC2U+pZereFti2IY74Eup6y2Po7TqOBdvPn343fSpSlKUNtsststt"
    "ttttsMMMMMNssoepd22229Syyyyyyw98H1LV+bZZY8xDtXjtdmvt3PueBqf7tp9vb8cDosjDi22GGHuIgglllttiIi3q3giU"
    "RKWZYbeC6llttl4IhiIifU56pbbbfqGtuHAvdvO8ER6BShlDDbMstsvG228DDDDbFst2S6l3bbbLLLLLLLLD3KXUu0ssseYn"
    "oHy9s8MnbwvWeen8Qx95em3l6PbkIGdyyyyw7ERENvUNsMMQ8KWWWOFKZbbbYYiPNucC9p9SwZ87xtvA95dT153nbY5UpShh"
    "ht4LPG2y22922wwyhthtll3wO222WWWWWWW2XfBS9stvBHA9vLaFnuy74PuYXZZ+D6jzdCyJfEtsPBBGDPMvUxiy8Dghht64"
    "2GGGGGZSyw9Wyn1LLLLzvURdZDwZywbzxvB5us9iXfp3uPEPBwpSlDKGG22WWWW222221hhhthtlhlLu222WWWWW2WWcp9Nt"
    "sseIuw+/T+LL7M5tl0nn3fBEZervlbwXvCEHl72yy5Ltt7xBFsQ29cbDeUMNssszD1b3KUstttsclseY8Sy7n6NvMlwu623j"
    "Yuthhi22UpShhhhttllllttthtthhhtttlb3OXdtttssssssts59WC/FvVsOx4kQHu5IXHi0V4MBe/B22x/pEci4JeSCZ9oz"
    "8rd8y8DyO442IYt6t4GUMPCyyyxbKctts8e8XvDwR4lhPVlr6NvKXXmfc877RHmPEc7DKUoYYbbbZZZbberbYbbYYeDbbZbe"
    "5S7lttllllllltlPq7FtvAhi/g/92Q/f/EpvLPH3Pb+LywvBaL9dS5IWnXvGeH7439XThLbe8Qce9sMob242GUoeFlLMNvcp"
    "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"
    "/B5mNB2997le1X7ZdnpvvK6YPeMqdf8A4Y/V2PvruGVfIz4mSyyyyy7u+DnLLLqyyyyyy6ssssss9D59BZZJBBBBCSS97CDq"
    "yyyyCPMeYOUmyyyzjLLLLLLPuyyySyyyyzgLLLLLGyyyyyyOMggHmQ8Qx4XhOrF7EB8rD95+WEvY2fnX4Jh878sqb8CIj3Hy"
    "+LQ/EC8h37L3JQ0RPq8zu1LbGX5ujff2Ju/h/wBxg2P80e+nxfbK/wD5q9nuoLudxk6s5yzj+OMgssssssssssssssssssss"
    "su7JLLLPQEEEEkkklllllkFkGwWWWSSWWWWWWWWWWWWfmyyyyyyyyxsssk/xghkHAO7CyzLN97KOh/N4kT7j6IjpF92Lxv1O"
    "ew+WxG/CCc7H8zrdHwLHfP55PSwDX+IkXz4fM7pCSBYB7Ql0eK077dj3h2xD0+kNWWegHaZlnJl+V+V+V+d0vy4fnflwxY4A"
    "5Hg/P0h+fAhCMYxn5X5cP5cDgIchjHt5ul+VlnJ+VllkegPLk/L0h2vyvxv5/wCF+PSvdu/FvlHwMl+XLJmz7j2U/BfAXO66"
    "/qS6lfu8+r2fecScTPb/ABZ32JXu+ngsUVx7WOPYPidDqT34H5zpdfSX48fx5z6zfx4/jfjfjfjw/H/H/wCcf48fw9G/Djv4"
    "j6xTiaxvfn6X4X4xxFPrb4PefQ/4/wCP/wDHpvfxbt+h/wBJf0l/T39Nf1d/V23/AM7+jv6e+u/iB/8Ahd//AKL+qv6qP+kv"
    "6y/qr+sv6i/oI+d+o/8ATE+Z+ifk/q+1+r7X6v8AoUZe5+J/6Sc//RZGv4sl3z/V/RX2f1IfP9SfGH4v6y0/+V/SR/1kY/8A"
    "Vff/AFb+/wDV8K/V/VX9Zf0l/WX9Bf1l/WR/0k/9JZf/ACv6ziv6K/pL+iv6e/o7+nv6O/p7+lv6e/q7+rv6a/rr7f6vvfqP"
    "+mv6i/quG/rL7n6vufq+xfc/Vr4f6j/qI/6y/wCnX9Zf9AgeVK+GV8N9yP8Apr+uj/or+osv/lYPbj5lv4YSD/qr+kv+mX9b"
    "f1l/SXzfqvsfq+5+o+R+r7X6vn/Rf0l8i/Us9m/C18WnhQ/j9V/WX9XH/W39Zf1t/W39Xf1d/RX2v3fY/d9j+77H932P3fY/"
    "d9j932P3fY/d9j+77H7tPd+77H9x8z+4+R/d9j+74F/cfK/u0e793wL+75D9z8j+77n933P7te63la7Ye79z7K/d9792Bqv4"
    "2Wf/AGX2P7vsf3K928QWfmfnfufmfu7/AC/d9r932P3PyP7vsb7G+x/d9j+77H7vuf3fc/d9z+77n933P7vvfu+1+77H932N"
    "9jfEv7ujy/cfI/d/cX9xf3F/cX9hf3F/dX3P3f3F9z+5T3f3b+X92/l/dr5f3fc/c/M/u18v7tfLa+W18sr5f3Kfdvsf3PzP"
    "7vufu/uL+8v7iV8v7l/Lx18t9l9j+74F/d9z933P7vsb7H92vn/cfI/u+5+7+4vufu+x+7737vufu+5/d9ja+7Xy2vltfL+7"
    "7H92n3bdr5hw/lvsf3fc/uP+4v7C/uG/vL+8vufuf+wj5H7tvNtttttvA922lvVv3bb93XxPzZ+M3t78gyIc7ZPzbaBrOneG"
    "xYmDPAzYe5c79Ibyb98i/dtv3yD6BvJtvoH5H+A48D6Qdr8o5G8N79QPyt9AJ4W2222228Nttttttt4bb6NtvN/POc5ZxnDz"
    "vIzbbbbY2+0Odswtz8zrzw2GWdHn3nExZbYZjwbaf4Qh+v8A5X/iaHXx/gBHAtvcvpDbbeQ5A2228b9Wttv1bbbbwG2HjfRt"
    "r8X8W/i/Hj+M8bxZZlhdWWF1M5PoAg+brjBuifPnjq6lDx5lJybqI8TLKS228NTr0D8rXzLatWrVq1atcmvrk2222221bbLM"
    "1a222222/cNuW+htbbW223jYbbYbY5yzLWWHlsW2ww223UZdXUYWnoHaZ3JPF5z/AIIAZcO0MZ/Mx5Dk+5r9uR4BGseDbbbb"
    "ZbbbbZeG22/dtttttvDbZbbeG8CDtsstuW23n0bDbbHpfPoH1bDbxvHcyW28Nt6ttj0gITXI83x4teJnlyay2vOw8bGxbni1"
    "bbYZxMWW1lbeS2222+hbbW2GW2222222237tttttttttttthtibvjWN9HfByMySSSWej247tbWG2GG3h4STPFrbbbba2tvIc"
    "ByHkJ+Z9QG8N4HnuOBHjjeN4WWZlttiCWXnf8j6t5223neP3bbDHmI6vMwzxs8PBe8c5JJJZx78EknpHqG2HlOElE87bxvG2"
    "28Fl4bbbbb6Mssss9HmPdZznOzx3LN3HmF4Jd2c56M4fPDwzxllllnrz1Hm94izjPRllllhEeYi8wSTMsss9GbJZZZF7xHA8"
    "5ZO5D/DvCv8AgyyyyyyyyyyEsEgv4ssssnxPnhOHxZfxD64B5nzxl/E/iyyyzh885JP+bLLLLqL+I5PxNnGcHdlllkERHnjJ"
    "LLLLL+LI/EXhJP4s4IjgjjIkPMwZR7ejbd8yT1bxklllllkEEfSJlllkwmMWWQWWWTMyctkTwWYXw+bLLPQ8sze3De/Gej29"
    "O+vrgj/ARd2NllkcHmOMkkks5LOE2ZlnoIi9+S+pJ6TuQ9Hi35sGyyyyyyIcggWWWWbHeMcZBZHDMzxk2cjwcO7ZZZZZZZ6H"
    "zPBM+bP8B6sj0EcZ6yOM2zg4PMXxEm3hMyyzIss7iY/CSyyyOuDjYeDzxkxgyJ59A5f/2Q=="
)


if __name__ == "__main__":
    main()
