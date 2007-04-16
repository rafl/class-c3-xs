use Module::Build;

use strict;

my $build = Module::Build->new(
    module_name => 'Class::C3::XS',
    xs_files => { 'XS.xs' => 'lib/Class/C3/XS.xs' },
    license => 'perl',
    optional => {},
    requires => {
        'perl'       => 5.008000,
    },
    build_requires => {
        'Test::More' => '0.47',
    },
    create_makefile_pl => 'traditional',
    create_readme => 1,
    recursive_test_files => 1,
    add_to_cleanup => [
        'META.yml', '*.bak', '*.gz', 'Makefile.PL',
        'XS.c', 'XS.o', 'XS.bs',
    ],
);

$build->create_build_script;

