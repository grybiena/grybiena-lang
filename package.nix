{ ps-pkgs, ... }:
  with ps-pkgs;
  { version = "1.0.0";
    dependencies =
      [ fixed-points
        matryoshka
        ordered-collections
        parsing
        prettier-printer
      ];
    src = "src";
   test-dependencies =
      [ test-unit
        console
      ];
    test-src = "test";
  }
