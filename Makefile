IDRIS ?= idris2
SRC_DIR = src
TRGT = Skeletons
IDR_FILES := $(SRC_DIR)/Skeletons/Farm.idr
IDR_FILES += $(SRC_DIR)/Skeletons/PipePL.idr
IDR_FILES += $(SRC_DIR)/Skeletons/BuffChanPL.idr
IPKG_FILE = $(TRGT).ipkg

all: $(TRGT)

build: $(TRGT)

$(TRGT): $(IDR_FILES)
	$(IDRIS) --build $(IPKG_FILE)

install: $(TRGT)
	$(IDRIS) --install $(IPKG_FILE)

.PHONY: all build clean

clean:
	$(RM) -r build

