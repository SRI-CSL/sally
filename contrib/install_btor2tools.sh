#!/bin/bash
set -e

echo "Installing btor2tools..."

# Clone the repository
if ! git clone https://github.com/hwmcc/btor2tools.git; then
    echo "Error: Failed to clone btor2tools repository." >&2
    exit 1
fi

# Navigate to btor2tools directory
if ! pushd btor2tools; then
    echo "Error: Failed to enter btor2tools directory." >&2
    exit 1
fi

# Run configure script
if ! ./configure.sh; then
    echo "Error: Configuration failed." >&2
    popd > /dev/null 2>&1
    exit 1
fi

# Enter build directory
if ! pushd build; then
    echo "Error: Failed to enter build directory." >&2
    popd
    exit 1
fi

# Run make
if ! make; then
    echo "Error: Build failed." >&2
    popd; popd
    exit 1
fi

# Return to original directories
popd
popd

echo "btor2tools installation completed successfully!"