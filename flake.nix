{
  description = "A Flake for my Independent Study with Tej Chajed";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
  in {
    devShells."${system}".default = let
      pkgs = import nixpkgs {
        inherit system;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "8d13c771b9a80957089f7c5b0ee2ccf58e5eb06f";
          sha256 = "1fbqs75ya4as3my2knkaq4m0crdh3n004grw5g5iczvb5h5k06lz";
        };
        vendorHash = "sha256-HCJ8v3TSv4UrkOsRuENWVz5Z7zQ1UsOygx0Mo7MELzY=";
      };
    in
      pkgs.mkShell {
        # create an environment with the required coq libraries
        packages = with pkgs; [
          # Coq deps
          coq

          # Go deps
          go
          gopls
          goose

          # Protobuf deps
          protobuf
          protoc-gen-go
          proto-contrib
          protoscope

          # nix helpers
          # Should be able to update goose and grackle with `update-nix-fetchgit flake.nix`
          pkgs.update-nix-fetchgit
          pkgs.nix-prefetch-git
          pkgs.nix-prefetch
        ];

        shellHook = ''
        '';
      };
  };
}
