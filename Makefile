all:
	$(MAKE) -C aam
	$(MAKE) -C fnd
	$(MAKE) -C cti

clean:
	$(MAKE) -C aam clean
	$(MAKE) -C fnd clean
	$(MAKE) -C cti clean

.PHONY: all clean
