use Module::Build;

use strict;

my $build = Module::Build->new(
    module_name => 'Class::C3::XS',
    license => 'perl',
    optional => {},
    build_requires => {
        'Test::More' => '0.47',
        'Test::Exception' => 0.15,
    },
    create_makefile_pl => 'traditional',
    create_readme => 1,
    recursive_test_files => 1,
    add_to_cleanup => [
        'META.yml', '*.bak', '*.gz', 'Makefile.PL',
    ],
);

$build->create_build_script;

