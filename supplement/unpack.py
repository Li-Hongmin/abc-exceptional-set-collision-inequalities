"""Extract the certificate archive (standard library only).

    python3 unpack.py            # writes the *.json files next to this file

The archive certificates.tar.xz contains the JSON branch-and-bound trees read by
check_starstar.py and check_lambda.py.  CONTENTS.sha256 lists the SHA-256 of every
file of the supplement including the extracted ones, so after extraction

    shasum -a 256 -c CONTENTS.sha256        (or  sha256sum -c CONTENTS.sha256)

checks both the packaged files and the extraction.
"""
import pathlib
import tarfile

HERE = pathlib.Path(__file__).resolve().parent
ARCHIVE = HERE / "certificates.tar.xz"
TARGET = HERE


def main():
    with tarfile.open(ARCHIVE, "r:xz") as tf:
        members = [m for m in tf.getmembers()
                   if m.isfile() and not pathlib.PurePosixPath(m.name).name.startswith("._")]
        for m in members:
            name = pathlib.PurePosixPath(m.name).name
            if not name.endswith(".json") or "/" in name:
                raise SystemExit(f"unexpected member {m.name}")
            with tf.extractfile(m) as src, open(TARGET / name, "wb") as dst:
                dst.write(src.read())
            print(f"extracted {name} ({m.size} bytes)")
    print(f"{len(members)} files written to {TARGET}")


if __name__ == "__main__":
    main()
