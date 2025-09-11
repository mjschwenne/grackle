{
  buildGoModule,
  fetchFromGitHub,
}: let
  pname = "goose";
  version = "0.9.2-unstable-2025-09-09";
  src = fetchFromGitHub {
    owner = "goose-lang";
    repo = "goose";
    rev = "cc3ebb8fef346ce83e7e8b49889e706eeaa5a004";
    hash = "sha256-eIQoIFuwRAn3TvO2A+f659NjdqV+c6FRufYmN+j2LYo=";
  };
in
  buildGoModule {
    inherit pname version src;
    proxyVendor = true;
    vendorHash = "sha256-MHo+sm5MUP5NVn128vu02zVcs2gpg24zC8o+UvBOnpI=";
  }
