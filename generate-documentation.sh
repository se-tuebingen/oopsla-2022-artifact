#!/usr/bin/env bash
pandoc -V colorlinks=true -V linkcolor=blue -V geometry:margin=2cm README.md GETTING-STARTED.md STEP-BY-STEP.md -o documentation.pdf
