.PHONY: all

all: FO-prover

FO-prover: FO-prover.hs *.hs
	ghc -package parsec -package mtl -o FO-prover FO-prover.hs

clean:
	rm FO-prover *.hi *.o