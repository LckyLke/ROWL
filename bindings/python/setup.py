"""Build the Rust library with cargo and ship it inside the `rowl` package."""
import os
import shutil
import subprocess
import sys
from pathlib import Path

from setuptools import setup
from setuptools.command.build_py import build_py
from setuptools.dist import Distribution

ROOT = Path(__file__).resolve().parents[2]


def library_name():
    if sys.platform == "darwin":
        return "librowl_python.dylib"
    if sys.platform == "win32":
        return "rowl_python.dll"
    return "librowl_python.so"


class BuildWithCargo(build_py):
    """Run `cargo build --release -p rowl-python` and copy the library."""

    def run(self):
        super().run()
        subprocess.run(["cargo", "build", "--release", "-p", "rowl-python"], cwd=ROOT, check=True)
        target = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
        built = target / "release" / library_name()
        destination = Path(self.build_lib) / "rowl" / library_name()
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(built, destination)


class BinaryDistribution(Distribution):
    """The package ships a native library, so its wheels are platform specific."""

    def has_ext_modules(self):
        return True


setup(cmdclass={"build_py": BuildWithCargo}, distclass=BinaryDistribution)
