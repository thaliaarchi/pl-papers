COQ_DIRS := aam fnd cti
RUST_DIRS := cti

all: coq rust

coq: $(COQ_DIRS)

rust:
	cargo build

$(COQ_DIRS)::
	$(MAKE) -C $@

$(RUST_DIRS)::
	cd $@ && cargo build

clean: clean-coq clean-rust

clean-coq:
	@$(foreach d,$(COQ_DIRS),$(MAKE) -C $(d) clean;)

clean-rust:
	cargo clean

.PHONY: all coq rust $(COQ_DIRS) $(RUST_DIRS) clean clean-coq clean-rust
