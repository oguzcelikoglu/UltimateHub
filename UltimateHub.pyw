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
import io
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


def build_tiff(byteorder, ifd0, exif_ifd, thumb=None):
    """Return EXIF as raw TIFF bytes (IFD0 + Exif IFD + optional thumbnail)."""
    bo = "<" if byteorder == "II" else ">"
    header = (b"II*\x00" if byteorder == "II" else b"MM\x00*") + struct.pack(bo + "I", 8)
    thumb_entries = []
    if thumb:
        thumb_entries = [
            (0x0103, 3, 6), (0x011A, 5, (72, 1)), (0x011B, 5, (72, 1)),
            (0x0128, 3, 2), (0x0201, 4, 0), (0x0202, 4, len(thumb)),
        ]

    # Pass 1: measure (sizes do not depend on the pointer values).
    len0 = len(_ifd_bytes(ifd0 + [(0x8769, 4, 0)], 8, bo, 0))
    off_exif = 8 + len0
    len_exif = len(_ifd_bytes(exif_ifd, off_exif, bo, 0))
    off1 = off_exif + len_exif
    off_thumb = off1
    if thumb:
        off_thumb = off1 + len(_ifd_bytes(thumb_entries, off1, bo, 0))

    # Pass 2: real offsets.
    out = bytearray(header)
    out += _ifd_bytes(ifd0 + [(0x8769, 4, off_exif)], 8, bo, off1 if thumb else 0)
    out += _ifd_bytes(exif_ifd, off_exif, bo, 0)
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

    def __init__(self, tiff, summary, phone, when, iso, exposure, fnum, software):
        self.tiff = tiff
        self.summary = summary
        self.phone = phone
        self.when = when
        self.iso = iso
        self.exposure = exposure
        self.fnum = fnum
        self.software = software


def pick_phone(rng=None):
    rng = rng or secrets.SystemRandom()
    return rng.choice(PHONES)


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
                     thumbnail=None, rng=None, now=None):
    """Generate a complete, self-consistent EXIF block for `phone`."""
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

    tiff = build_tiff(phone["byteorder"], ifd0, ex, thumbnail)
    shutter = "1/%d s" % exposure[1] if exposure[0] == 1 else "%g s" % t_real
    summary = "{}{}  |  {:%Y-%m-%d %H:%M}  |  ISO {}  |  f/{:g}  |  {}".format(
        phone["label"], "  (" + (software or "") + ")" if software else "",
        when, iso, n, shutter)
    return ExifResult(tiff, summary, phone, when, iso, exposure, n, software)


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

class RandomExif:
    """Request to write a random phone's EXIF into the exported image."""

    def __init__(self, rng=None, phone=None):
        self.rng = rng or secrets.SystemRandom()
        self.phone = phone or pick_phone(self.rng)
        self.result = None

    def make(self, width, height, orientation, color_space, thumb_image):
        thumb = make_thumbnail(thumb_image) if thumb_image is not None else None
        self.result = build_phone_exif(self.phone, width, height, orientation,
                                       color_space, thumb, rng=self.rng)
        return self.result.tiff


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
            options = dict(format="JPEG", quality=100 if maximum else 95,
                           subsampling=0, optimize=True)
            if exif_bytes:
                options["exif"] = b"Exif\x00\x00" + exif_bytes
            clean.save(destination, **options)
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
    notes = []

    if keep_format and source_format == "JPEG":
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
            random_exif.result = build_phone_exif(
                random_exif.phone, width, height, orientation, space, thumb, rng=random_exif.rng)
            strip_jpeg_metadata(source, destination,
                                exif_app1=exif_app1_segment(random_exif.result.tiff),
                                keep_jfif=False)
    elif keep_format and source_format == "PNG":
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
                    random_exif.result = build_phone_exif(
                        random_exif.phone, width, height, orientation, 1, thumb,
                        rng=random_exif.rng)
                    exif_tiff = random_exif.result.tiff
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
        self.status = tk.StringVar(value="Choose an image to get started.")
        self.file_info = tk.StringVar(value="No image selected")
        self.build_ui()

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

        content = tk.Frame(outer, bg=WHITE)
        content.pack(fill="both", expand=True, padx=24, pady=(16, 8))
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
            left, bg=WHITE, fg=TEXT_DIM, font=F(8), justify="left", anchor="w", wraplength=300,
            text="Instead of a clean file, the copy gets realistic EXIF data (model, lens, ISO, "
                 "exposure, brightness, date...) of a random popular phone out of 30.")
        self.exif_hint.pack(anchor="w", fill="x", pady=(2, 0))

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
        tk.Label(right, bg=WHITE, fg=TEXT_DIM, font=F(8), justify="left", anchor="w", wraplength=340,
                 text="Maximum quality uses lossless WebP and quality 100 for JPEG, HEIC/HEIF and "
                      "AVIF. PNG and TIFF are always lossless. JPEG, GIF, HEIC/HEIF and AVIF "
                      "conversions may lose detail; transparency or animation may change."
                 ).pack(anchor="w", fill="x")

    # ------------------------------------------------------------- actions
    def effective_format(self):
        target, _ = CONVERSION_FORMATS[self.output_format.get()]
        return target or self.source_format

    def update_exif_hint(self):
        fmt = self.effective_format()
        if self.random_exif.get() and fmt and fmt not in EXIF_FORMATS:
            self.exif_hint.configure(
                fg="#B05A00",
                text=f"{fmt} files cannot store EXIF. The copy will be saved without metadata. "
                     "Pick JPEG, PNG, WebP, HEIC or AVIF to write random EXIF.")
        else:
            self.exif_hint.configure(
                fg=TEXT_DIM,
                text="Instead of a clean file, the copy gets realistic EXIF data (model, lens, "
                     "ISO, exposure, brightness, date...) of a random popular phone out of 30.")

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
            self.source_path = path
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
            request = RandomExif() if self.random_exif.get() else None
            notes, summary = export_clean_image(
                self.source_path, temp, target_format, self.quality_mode.get(), request)
            os.replace(temp, destination)
            self.status.set(f"Saved: {destination}")
            lines = [f"Saved file:\n{destination}"]
            if summary:
                lines.append(f"Random EXIF written:\n{summary}")
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
        tk.Label(body, bg=WHITE, fg=TEXT_DIM, font=F(9), justify="left", anchor="w",
                 text="It keeps running in the background when you go back to the tool list. "
                      "NumLock must be on. Press Num - to switch mouse control on or off."
                 ).pack(anchor="w", pady=(6, 0))

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
        self.window = AeroWindow(root, APP_NAME, taskbar=True, min_size=(780, 540),
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
        page = tk.Frame(self.window.client, bg=WHITE)
        page.pack(fill="both", expand=True)

        # bottom pane first, so it always stays visible
        bottom = tk.Frame(page, bg=DETAILS_BG)
        bottom.pack(side="bottom", fill="x")
        tk.Frame(bottom, bg=BAR_BORDER, height=1).pack(fill="x")
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

        body = tk.Frame(page, bg=WHITE)
        body.pack(fill="both", expand=True)
        self.nav = tk.Frame(body, bg=NAV_BG, width=self.NAV_WIDTH)
        self.nav.pack(side="left", fill="y")
        self.nav.pack_propagate(False)
        tk.Frame(body, bg="#D5DFEC", width=1).pack(side="left", fill="y")
        self.content = tk.Frame(body, bg=WHITE)
        self.content.pack(side="left", fill="both", expand=True)

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
            if tool["kind"] == "embedded":
                OpenImagePage(self, self.window.client)
            else:
                NuMousePage(self, self.window.client, tool)
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


if __name__ == "__main__":
    main()
