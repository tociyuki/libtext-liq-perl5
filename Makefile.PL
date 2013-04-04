use strict;
use warnings;
use ExtUtils::MakeMaker;

WriteMakefile(
    NAME                => 'Text::Liq',
    AUTHOR              => 'MIZUTANI Tociyuki <tociyuki@gmail.com>',
    VERSION_FROM        => 'lib/Text/Liq.pm',
    ABSTRACT_FROM       => 'lib/Text/Liq.pm',
    PL_FILES            => {},
    PREREQ_PM => {
        'Test::Base'    => 0,
        'Test::Exception' => 0,
        'Time::Piece'   => 0,
        'POSIX'         => 0,
        'Encode'        => 0,
        'Scalar::Util'  => 0,
    },
    dist                => { COMPRESS => 'gzip -9f', SUFFIX => 'gz', },
    clean               => { FILES => 'Text-Liq-*' },
);
