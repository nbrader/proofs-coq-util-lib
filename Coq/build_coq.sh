#!/bin/bash

# Clean up old Makefile
rm -f Makefile Makefile.conf

# Generate Makefile from _CoqProject
coq_makefile -f _CoqProject -o Makefile

# Check if Makefile exists
if [ ! -f Makefile ]; then
    echo "Makefile was not generated."
    exit 1
fi

# Build the project using the generated Makefile
make || { echo "Make failed"; exit 1; }
