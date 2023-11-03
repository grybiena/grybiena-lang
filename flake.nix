rec {
  description = "grybiena-lang";

  inputs = {
    env.url = "git+ssh://git@github.com/grybiena/purescript-environment?ref=grybiena";  
  };

  outputs = inputs@{ env, ... }:
    env.flake-utils.lib.eachDefaultSystem (system:
      env.build-package { inherit system;
                          name = description;
                          src = ./.;
                          overlays = inputs;
                          derive-package = ./package.nix;
                        }
                
   );
}

