# LeanSISSA website

The site is a Verso manual. The source code is in `Main.lean`.

To set up the dependencies and build the site:

```sh
# Run this from the Website directory
lake update
lake exe cache get
lake build VersoManual
lake env lean --run Main.lean --output _site
python3 finish_site.py
```

Serve the generated files locally:

```sh
# Run this from the Website directory
python3 -m http.server 8000 --directory _site/html-multi
```

Open this at <http://localhost:8000/>.
