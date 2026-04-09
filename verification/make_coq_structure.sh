#!/bin/bash

# Base directory
BASE="coq/StrategicAbstraction"

# Create directories
mkdir -p "$BASE/Core"
mkdir -p "$BASE/Certificates"
mkdir -p "$BASE/InfoNCE"
mkdir -p "$BASE/Phenomena"
mkdir -p "$BASE/ImplementationSketch"

# Core files
touch "$BASE/Core/MarkovGame.v"
touch "$BASE/Core/Policy.v"
touch "$BASE/Core/Value.v"
touch "$BASE/Core/SoftBestResponse.v"
touch "$BASE/Core/StrategicDivergence.v"
touch "$BASE/Core/SEC.v"

# Certificates files
touch "$BASE/Certificates/OccupancyMeasure.v"
touch "$BASE/Certificates/PerformanceDifference.v"
touch "$BASE/Certificates/DSEC.v"
touch "$BASE/Certificates/EntropyBridge.v"

# InfoNCE files
touch "$BASE/InfoNCE/Loss.v"
touch "$BASE/InfoNCE/OptimalCritic.v"
touch "$BASE/InfoNCE/Rademacher.v"
touch "$BASE/InfoNCE/VCClassification.v"

# Phenomena files
touch "$BASE/Phenomena/HorizonEquivalence.v"
touch "$BASE/Phenomena/Diversity.v"

# ImplementationSketch files
touch "$BASE/ImplementationSketch/Algorithms.v"
touch "$BASE/ImplementationSketch/Diagnostics.v"

echo "✔ Coq directory structure created."

