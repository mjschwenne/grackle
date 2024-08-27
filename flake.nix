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
      coq = pkgs.coq;
      coqv = coq.coq-version;
      coq-tactial = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-tactial";
        src = pkgs.fetchFromGitHub {
          owner = "tchajed";
          repo = "coq-tactical";
          rev = "7c26f9a017395c240845184dfed23489d29dbae5";
          hash = "sha256-SNoQzGYw5tuabHUDwMAyUsAa/WNoYjmyR85b7a0hVl4=";
        };
        buildInputs = [coq];
        buildPhase = ''
          make -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r src $out/lib/coq/${coqv}/user-contrib/Tactical
        '';
      };
      coqutil = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-coqutil";
        src = pkgs.fetchFromGitHub {
          owner = "mit-plv";
          repo = "coqutil";
          rev = "0833256bce2a55642c2b0ca37be6bbd27e1af6e1";
          hash = "sha256-aEDdIq/pg+C1zKkcITVYLr87Z1C0b+4/4Z2pHqr7hVY=";
        };
        buildInputs = [coq];
        buildPhase = ''
          make -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r src/coqutil $out/lib/coq/${coqv}/user-contrib/
        '';
      };
      stdpp = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-stdpp";
        src = pkgs.fetchFromGitLab {
          owner = "iris";
          repo = "stdpp";
          domain = "gitlab.mpi-sws.org";
          rev = "6190d85da4ef1408c12997edba85443c8d98f9a7";
          hash = "sha256-YPz+OUlwaf9Wm6iGJr7ATwXUFFWbjHCl4+JY6ExhMA8=";
        };
        buildInputs = [coq pkgs.time];
        nativeBuildInputs = [coqutil];
        buildPhase = ''
          export COQPATH=${coqutil}/lib/coq/${coqv}/user-contrib:$COQPATH
          if [[ -f coq-lint.sh ]]
          then patchShebangs coq-lint.sh
          fi
          make TIMED=false -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r stdpp $out/lib/coq/${coqv}/user-contrib
        '';
      };
      iris = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-iris";
        src = pkgs.fetchFromGitLab {
          owner = "iris";
          repo = "iris";
          domain = "gitlab.mpi-sws.org";
          rev = "657b34ad877f1ba22414e0e85ad2a49e56a188e0";
          hash = "sha256-H1iHKu33ROCBolAKTwI3GSuL3Ttgrx4bhUbom04Sdo4=";
        };
        buildInputs = [coq pkgs.time];
        nativeBuildInputs = [stdpp];
        buildPhase = ''
          export COQPATH=${stdpp}/lib/coq/${coqv}/user-contrib:$COQPATH
          if [[ -f coq-lint.sh ]]
          then patchShebangs coq-lint.sh
          fi
          make TIMED=false
        '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r iris $out/lib/coq/${coqv}/user-contrib
          cp -r iris_heap_lang $out/lib/coq/${coqv}/user-contrib/iris/heap_lang
          cp -r iris_unstable $out/lib/coq/${coqv}/user-contrib/iris/unstable
        '';
      };
      iris-named-props = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-iris-named-props";
        src = pkgs.fetchFromGitHub {
          owner = "tchajed";
          repo = "iris-named-props";
          rev = "1b155dcba80036381d1088ef10689317fb67f7f2";
          hash = "sha256-mB1ZnfX58RyCsPD177dGVNQWo6WikrDVIRiaAn3efD0=";
        };
        buildInputs = [coq pkgs.time];
        nativeBuildInputs = [stdpp coqutil iris];
        buildPhase = ''
          export COQPATH=${stdpp}/lib/coq/${coqv}/user-contrib:${coqutil}/lib/coq/${coqv}/user-contrib:${iris}/lib/coq/${coqv}/user-contrib:$COQPATH
          make TIMED=false -j$NIX_BUILD_CORES
        '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r src $out/lib/coq/${coqv}/user-contrib/iris_named_props
        '';
      };
      coq-record-update = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-record-update";
        src = pkgs.fetchFromGitHub {
          owner = "tchajed";
          repo = "coq-record-update";
          rev = "e2aaf327d54a1c2f77e77e8e601284e829f292dc";
          hash = "sha256-H3fYqtzAA84kCAFd78ZDx/z+xbNokk5PKbXt2xr4GNU=";
        };
        buildInputs = [coq];
        installPhase = ''
          mkdir -p $out/lib/coq/${coqv}/user-contrib
          cp -r src $out/lib/coq/${coqv}/user-contrib/RecordUpdate
        '';
      };
      perennial = pkgs.stdenv.mkDerivation {
        name = "coq${coqv}-perennial";
        src = pkgs.fetchFromGitHub {
          owner = "mit-pdos";
          repo = "perennial";
          rev = "a908febd36592e3d88d3dd657a1a861720f32a45";
          # fetchSubmodules = true;
          # hash = "sha256-+FfFaeIBTrzkIUyqNfcm9/fzpzrkaaltPHZSZcHed40="; # with submodules
          fetchSubmodules = false;
          hash = "sha256-EvrX8qJE4b7m0LXSCaL2XQWFeBCve6HkZK6h9e/ta8g="; # without submodules
        };
        buildInputs = [coq];
        nativeBuildInputs = [stdpp coq-record-update iris iris-named-props coqutil coq-tactial];
        buildPhase =
          /*
          bash
          */
          ''
            export COQPATH=${stdpp}/lib/coq/${coqv}/user-contrib:${iris}/lib/coq/${coqv}/user-contrib:${iris-named-props}/lib/coq/${coqv}/user-contrib:${coq-record-update}/lib/coq/${coqv}/user-contrib:${coq-tactial}/lib/coq/${coqv}/user-contrib:${coqutil}/lib/coq/${coqv}/user-contrib:$COQPATH
            echo $COQPATH
            make TIMED=false -j$NIX_BUILD_CORES
          '';
        installPhase = ''
          mkdir -p $out/lib/coq/${coq.coq-version}/user-contrib
          cp -r src $out/lib/coq/${coq.coq-version}/user-contrib/Perennial
        '';
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
        packages = [
          # Coq deps
          coq
          stdpp
          coq-record-update
          iris
          iris-named-props
          coq-tactial
          coqutil
          perennial

          # Go deps
          pkgs.go
          pkgs.gopls
          goose
        ];

        shellHook = ''
          export COQPATH=${coq-tactial}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${coqutil}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${coq-record-update}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${stdpp}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${iris}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${iris-named-props}/lib/coq/${coqv}/user-contrib:$COQPATH
          export COQPATH=${perennial}/lib/coq/${coqv}/user-contrib:$COQPATH
        '';
      };
  };
}
