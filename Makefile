SRC_DIRS := 'perennial' 'new_example' 'testdata/out'
ALL_VFILES := $(shell find $(SRC_DIRS) -not -path "perennial/external/coqutil/etc/coq-scripts/*" -name "*.v")
PROJ_VFILES := $(shell find 'new_example' -name "*.v")

# extract any global arguments for Rocq from _RocqProject
ROCQ_PROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)

# user configurable
Q:=@
ROCQ_ARGS := -noglob
ROCQ_C := rocq compile

default: vo

vo: $(PROJ_VFILES:.v=.vo)
vos: $(PROJ_VFILES:.v=.vos)
vok: $(PROJ_VFILES:.v=.vok)

all: vo

.rocqdeps.d: $(ALL_VFILES) _RocqProject
	@echo "ROCQ DEP $@"
	$(Q)rocq dep -vos -f _RocqProject $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .rocqdeps.d
endif

%.vo: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE $<"
	$(Q)$(ROCQ_C) $(ROCQ_PROJECT_ARGS) $(ROCQ_ARGS) -o $@ $<

%.vos: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vos $<"
	$(Q)$(ROCQ_C) $(ROCQ_PROJECT_ARGS) -vos $(ROCQ_ARGS) $< -o $@

%.vok: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vok $<"
	$(Q)$(ROCQ) $(ROCQ_PROJECT_ARGS) -vok $(ROCQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	$(Q)rm -f .timing.sqlite3
	rm -f .rocqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
