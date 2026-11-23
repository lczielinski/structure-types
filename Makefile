FSTAR = fstar.exe $(shell python3 -c "import json; print(*json.load(open('.fst.config.json'))['options'])") \
  --cache_checked_modules --cache_dir .cache --already_cached 'Prims FStar'
SRC = $(wildcard src/*.fst src/*/*.fst src/*/*.fsti programs/*.fst)

all: $(patsubst %,.cache/%.checked,$(notdir $(SRC)))

.depend: $(SRC)
	$(FSTAR) --dep full $^ -o $@

-include .depend

%.checked:
	$(FSTAR) $< && touch -c $@

clean:
	rm -rf .cache .depend
