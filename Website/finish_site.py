"""Add the local style and tab enhancement to Verso's HTML output."""
from pathlib import Path
import re
import shutil

root = Path(__file__).resolve().parent
site = root / '_site' / 'html-multi'
if not (site / 'index.html').exists():
    raise SystemExit('Build the Verso site before running this script.')
for name in ('site.css', 'site.js'):
    shutil.copyfile(root / name, site / name)
assets = ('<link data-course-assets rel="stylesheet" href="site.css">'
          '<script defer src="site.js"></script>')
for page in site.rglob('*.html'):
    text = page.read_text(encoding='utf-8')
    # Verso sets a base URL pointing to the site root on every page.
    text = re.sub(r'<link data-course-assets[^>]*><script defer src="[^"]*site\.js"></script>', '', text)
    page.write_text(text.replace('</head>', assets + '</head>', 1), encoding='utf-8')
