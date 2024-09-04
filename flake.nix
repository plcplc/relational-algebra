{
  description = "Relational Algebra DSL";

  inputs = {
    flake-utils = {
      url = github:numtide/flake-utils;
    };

    nixpkgs = {
      # url = github:NixOS/nixpkgs/nixos-22.11;
      url = github:NixOS/nixpkgs/nixos-unstable;
    };
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {inherit system;};
      nixos = import "${nixpkgs}/nixos";
      ghcName = "ghc945";
      hsPackageOverrides = pkgsNew: pkgsOld: rec {
        relational-algebra = pkgsNew.callPackage ./default.nix {};
      };
      hs = pkgs.haskell.packages.${ghcName}.override {overrides = hsPackageOverrides;};
    in rec {
      formatter = pkgs.alejandra;

      packages.relational-algebra = hs.relational-algebra;

      devShells.default = let
        doDistribute = pkgs.haskell.lib.doDistribute;
        dontCheck = pkgs.haskell.lib.dontCheck;
        jailbreak = pkgs.haskell.lib.doJailBreak;
        hs = pkgs.haskell.packages.${ghcName}.override {
          overrides = hsPkgNew: hsPkgOld: rec {
            ghcid = dontCheck hsPkgOld.ghcid;
          };
        };
      in
        pkgs.mkShell {
          buildInputs = [
            # pkgs.zlib
            # pkgs.zlib.dev
            # pkgs.stdenv
            # pkgs.jq
            # pkgs.cabal2nix
            # pkgs.openssl
            # pkgs.just
            pkgs.alejandra

            (hs.ghcWithPackages (hsPkgs: with hsPkgs; packages.relational-algebra.buildInputs))

            hs.cabal-install
            hs.ghcid
            hs.haskell-language-server
            hs.ormolu
          ];
        };
    });
}
