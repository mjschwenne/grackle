{
  description = "A Flake for my Independent Study with Tej Chajed";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = {
    self,
    nixpkgs,
    ...
  }: let
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
          rev = "8c44ba97cb0bdc3aeffee8c88af20178241d0223";
          hash = "sha256-n56XASmaaAVHhtisN4vuf4Ip+NgIv8J7qoe7sY5we/U=";
        };
        vendorHash = "sha256-sI5HJmskJ+Qdf7lgbk2ztE4gfRY6YvR7wxK2g3knQko=";
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
        ];

        shellHook = ''
        '';
      };
  };
}
