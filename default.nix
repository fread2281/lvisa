{ mkDerivation, ansi-wl-pprint, base, basic-prelude, bytestring
, Cabal, constraints, containers, deepseq, ghc-prim
, ghc-typelits-knownnat, ghc-typelits-natnormalise, hashable, lens
, megaparsec, mtl, optparse-applicative, parsers, parsix, primitive
, QuickCheck, reflection, semigroups, singletons, stdenv, text
, transformers, unordered-containers, vault, vector
}:
mkDerivation {
  pname = "lvisa";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    ansi-wl-pprint base basic-prelude bytestring Cabal constraints
    containers deepseq ghc-prim ghc-typelits-knownnat
    ghc-typelits-natnormalise hashable lens megaparsec mtl
    optparse-applicative parsers parsix primitive QuickCheck reflection
    semigroups singletons text transformers unordered-containers vault
    vector
  ];
  description = "A dependently typed language with nice things";
  license = stdenv.lib.licenses.bsd3;
}
