mllex/mllex: mllex/poly-mllex.ML mllex/mllex.sml
	polyc -o $@ $<


QuoteFilter.sml: QuoteFilter mllex/mllex
	mllex/mllex $<

clean:
	-rm -f mllex/mllex QuoteFilter.sml



.PHONY: clean
