#!perl
use Test::More;

if (! -e '.author') {
    Test::More::plan(skip_all => "-e '.author'");
}
if (require Test::Perl::Critic) {
    my @arg;
    push @arg, -profile => 't/perlcriticrc' if -e 't/perlcriticrc';
    Test::Perl::Critic->import(@arg);
}
else {
    Test::More::plan(
        skip_all => "Test::Perl::Critic is not installed"
    );
}

Test::Perl::Critic::all_critic_ok();
