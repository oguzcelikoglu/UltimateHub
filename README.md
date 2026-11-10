# UltimateHub

A single-file Windows launcher with a Windows 7 "Aero" look. It bundles two small tools and lets you add any `.exe` to a Steam-library-style list.

Everything lives in one file: `UltimateHub.pyw`.

## Screenshots

![UltimateHub main window](hub.png)

![OpenImage](openimage.png)

## Features

**Hub**
- Windows 7 Aero styled window (glass title bar, Explorer-like navigation pane, details pane).
- **Add app**: pick any `.exe`; it is added with its icon and gets **Run** and **Delete** buttons. Delete only removes the entry, never the program.
- Search and filters (all / built-in / added apps / running).

**NuMouse**: control the mouse cursor with the numpad.
- Runs as a background helper: leaving its page does not stop it. Use **Stop** on its row or page.
- `Num -` toggles control, `8/2/4/6` move, `7/9/5` hold left/right/middle button, `0` slow, `3` and `,` scroll.
- While control is on, the keys it uses are blocked from other programs. NumLock must be on.

**OpenImage**: image privacy tool.
- Removes EXIF and other embedded metadata (JPEG and PNG are cleaned losslessly, without re-compression).
- Converts between JPEG, PNG, WebP, TIFF, BMP, GIF, HEIC/HEIF and AVIF.
- **Write random EXIF**: instead of leaving the file clean, it writes realistic EXIF of a random phone out of 30 built-in models (model, lens, ISO, exposure, brightness, date...). The goal is privacy: hiding your real device. The values are generated to be consistent with each other, but it is not a perfect forgery (for example, vendor MakerNote data is not included).

## Requirements

- Windows 10 / 11, Python 3.8+
- `pip install -r requirements.txt`

## Run

Double-click `UltimateHub.pyw`. The `.pyw` extension makes Windows start it without a console window.

For debugging you can also run it from a terminal: `python UltimateHub.pyw`.

## Build an .exe (optional)

```
pip install pyinstaller
pyinstaller --noconfirm --windowed --name UltimateHub UltimateHub.pyw
```

Antivirus software sometimes flags keyboard-hook tools like NuMouse in packaged builds. The `onedir` build above (the default) triggers fewer warnings than `--onefile`.

## Notes

- Added apps, their icons and tool logs are stored next to the script in `hub_data/`.
- If the custom window frame misbehaves on your system, set `USE_AERO_FRAME = False` near the top of the file to use the normal Windows title bar.

## License

MIT
