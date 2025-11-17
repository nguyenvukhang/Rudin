MAKEFILE_PATH   := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_DIR    := $(dir $(MAKEFILE_PATH))

LEAN_DIR        := $(MAKEFILE_DIR)..
CARGO_DEBUG_DIR := $(MAKEFILE_DIR)target/debug

CARGO_INSTALL := cargo install --locked --all-features --force

current: search

build:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino build

search:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino search

graph:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino graph

rg:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino rg

check-fmt:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino check-fmt

install:
	$(CARGO_INSTALL) --path .

run:
	cargo run -- generate Dino
