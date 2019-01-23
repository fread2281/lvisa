{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc863", f ? import ./default.nix }:

let

  inherit (nixpkgs) pkgs;

  haskellPackages = (if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler}).override {
  overrides = self: super: with pkgs.haskell.lib; {
    ghc = super.ghc // { withPackages = super.ghc.withHoogle; };
    ghcWithPackages = self.ghc.withPackages;
      cereal = dontCheck super.cereal;
      parsix = dontCheck super.parsix;
      # psqueues = doJailbreak super.psqueues;
      # singletons = doJailbreak super.singletons;
    };};

  drv = pkgs.haskell.lib.overrideCabal (haskellPackages.callPackage f {}) (drv: rec {
    buildDepends = (drv.buildDepends or []) ++ (with haskellPackages;
      [cabal-install ghcid
  ]);});

in drv.env
  #if pkgs.lib.inNixShell then drv.env else drv
