
all: cryptoverif

cryptoverif: 
	@(cd src && $(MAKE))

cryptoverif_dbg:
	@(cd src && $(MAKE) $@)

.PHONY: clean impl all cryptoverif dbg cryptoverif_dbg

clean:
	@(cd src && $(MAKE) $@)
	-rm cryptoverif cryptoverif_dbg


dbg:cryptoverif_dbg

