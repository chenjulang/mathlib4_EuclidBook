#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

set -x
cd $(dirname "$(realpath "$0")")

header() {
  cat <<EOF
# DO NOT EDIT THIS FILE!!!

# This file is automatically generated by mk_build_yml.sh
# Edit .github/build.in.yml instead and run mk_build_yml.sh to update.

# Forks of mathlib and other projects should be able to use build_fork.yml directly
EOF
}

build_yml() {
  header
  cat <<EOF
# The jobs in this file run on self-hosted workers and will not be run from external forks

on:
  push:
    branches-ignore:
      # ignore tmp branches used by bors
      - 'staging.tmp*'
      - 'trying.tmp*'
      - 'staging*.tmp'
      - 'nolints'
      # ignore staging branch used by bors, this is handled by bors.yml
      - 'staging'
  merge_group:

name: continuous integration
EOF
  include 1 pr == "" ubuntu-latest
}

bors_yml() {
  header
  cat <<EOF
# The jobs in this file run on self-hosted workers and will not be run from external forks

on:
  push:
    branches:
      - staging

name: continuous integration (staging)
EOF
  include 1 bors == "" bors
}

build_fork_yml() {
  header
  cat <<EOF
# The jobs in this file run on GitHub-hosted workers and will only be run from external forks

on:
  push:
    branches-ignore:
      # ignore tmp branches used by bors
      - 'staging.tmp*'
      - 'trying.tmp*'
      - 'staging*.tmp'
      - 'nolints'

name: continuous integration (mathlib forks)
EOF
  include 0 ubuntu-latest != " (fork)" ubuntu-latest
}

include() {
  sed "
    s/IS_SELF_HOSTED/$1/g;
    s/RUNS_ON/$2/g;
    s/MAIN_OR_FORK/$3/g;
    s/JOB_NAME/$4/g;
    s/STYLE_LINT_RUNNER/$5/g;
    /^#.*autogenerating/d
  " ../build.in.yml
}

build_yml > build.yml
bors_yml > bors.yml
build_fork_yml > build_fork.yml
