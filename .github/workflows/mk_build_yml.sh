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
# Edit .github/build.in.yml instead and run
# .github/workflows/mk_build_yml.sh to update.

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
  include "github.sha" pr "github.repository == 'leanprover-community\/mathlib4'" "" ubuntu-latest
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
  include "github.sha" bors "github.repository == 'leanprover-community\/mathlib4'" "" bors
}

build_fork_yml() {
  header
  cat <<EOF
# The jobs in this file run on self-hosted workers and will be run from external forks

on:
  pull_request_target:
    branches-ignore:
      # ignore tmp branches used by bors
      - 'staging.tmp*'
      - 'trying.tmp*'
      - 'staging*.tmp'
      - 'nolints'

name: continuous integration (mathlib forks)
EOF
  include "github.event.pull_request.head.sha" pr "github.event.pull_request.head.repo.fork" " (fork)" ubuntu-latest
}

include() {
  sed "
    s/PR_BRANCH_REF/$1/g;
    s/RUNS_ON/$2/g;
    s/FORK_CONDITION/$3/g;
    s/JOB_NAME/$4/g;
    s/STYLE_LINT_RUNNER/$5/g;
    /^### NB/d
  " ../build.in.yml
}

build_yml > build.yml
bors_yml > bors.yml
build_fork_yml > build_fork.yml
