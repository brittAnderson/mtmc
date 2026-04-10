{
  description = "Thoughts on a future, better psychology.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      ghcWithDeps = pkgs.haskellPackages.ghcWithPackages (hp: with hp;
        [
          hakyll
        ]);
    in
      {
        devShells.${system}.default = pkgs.mkShell {
          name = "mtmc";
          buildInputs = [
            ghcWithDeps
            pkgs.cabal-install
          ];
          shellHook = ''
            echo "Structure is function; function structure. That is all ye need to know."
          '';
        };
      };
  }
