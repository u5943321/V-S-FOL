mllex/mllex: mllex/poly-mllex.ML mllex/mllex.sml
	polyc -o $@ $<

clean:
	-rm -f mllex/mllex



.PHONY: clean
