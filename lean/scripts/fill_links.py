#!/usr/bin/env python3
"""Fill fixed-commit proof links and the browser link after publishing the proof sources."""
from pathlib import Path
import argparse
import json
import re
import subprocess
import sys
from urllib.parse import quote, urlparse

ROOT = Path(__file__).resolve().parents[2]
LINK_BLOCK = r"(?<=<!-- BEGIN PUBLICATION LINKS -->\n).*?(?=\n<!-- END PUBLICATION LINKS -->)"


def lean4web_line(repository, project="mathlib-stable"):
    """The README line that opens the single-file proof on the default branch in Lean4Web."""
    raw = repository.replace("https://github.com/", "https://raw.githubusercontent.com/")
    raw += "/main/lean4web/QubitStrongAdditivityLean4Web.lean"
    browser = "https://live.lean-lang.org/#project=" + quote(project, safe="") + "&url=" + quote(raw, safe="")
    toolchain = (ROOT / "lean4web/lean-toolchain").read_text().strip().rsplit(":", 1)[-1]
    version = ".".join(toolchain.split(".")[:2])
    line = f"**Try it in Lean4Web:** [open the complete proof in one file]({browser}) (Lean **{version}**)."
    return browser, line


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository_url")
    parser.add_argument("commit")
    parser.add_argument("--lean4web-project", default="mathlib-stable",
                        help="Project of the Lean4Web server that runs the single file")
    args = parser.parse_args()
    repository = args.repository_url.rstrip("/")
    parsed = urlparse(repository)
    if parsed.scheme != "https" or parsed.hostname != "github.com" or len(parsed.path.strip("/").split("/")) != 2:
        parser.error("Use a GitHub repository URL: https://github.com/OWNER/REPOSITORY")
    if not re.fullmatch(r"[0-9a-fA-F]{40}", args.commit):
        parser.error("Use the full 40-character commit SHA that contains the proof")
    commit = args.commit.lower()
    subprocess.run([sys.executable, str(ROOT / "lean/scripts/make_fc_statement.py"),
                    "--repository", repository, "--commit", commit,
                    "--output", str(ROOT / "FClikelean/QubitHolevoAdditivity.lean")], check=True)
    browser, block = lean4web_line(repository, args.lean4web_project)
    for path in (ROOT / "README.md", ROOT / "lean4web/README.md"):
        text = path.read_text()
        text = re.sub(LINK_BLOCK, lambda _: block, text, flags=re.S)
        path.write_text(text)
    metadata = {"repository_url": repository, "proof_commit": commit,
                "lean4web_url": browser, "lean4web_project": args.lean4web_project,
                "hosted_status": "lean4web/hosted-status.json"}
    (ROOT / "publication.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print("Filled fixed-commit publication links; no push or submission performed")
    print("The FC draft changed: run python3 comparator/refresh-pins.py and review comparator/pins.json")


if __name__ == "__main__":
    main()
