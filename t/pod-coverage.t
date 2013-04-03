#!perl -T
use Test::More;

if (! -e '.author') {
    plan skip_all => "-e '.author'";
}
eval "use Test::Pod::Coverage 1.04";
if ($@) {
    plan skip_all => "Test::Pod::Coverage 1.04 required";
}

all_pod_coverage_ok();
