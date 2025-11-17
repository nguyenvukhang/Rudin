LAKE_BUILD := lake build --log-level=warning

current: focus

focus: check
	lake-dino build Rudin

all: check
	lake-dino build

check: generate
	lake-dino check

generate:
	lake-dino generate Rudin.Partition
	lake-dino generate Rudin.Prelude
	lake-dino generate Rudin.Axioms

sorry:
	rg sorry -t lean --colors 'match:fg:yellow' --colors 'line:fg:white'

# First-time Setup =============================================================

setup:
	lake exe cache get

install:
	make -C fmt install

# Running Lean Binaries ========================================================

.PHONY: dino
