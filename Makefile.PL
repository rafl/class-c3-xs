use inc::Module::Install;

name           'Class-C3-XS';
all_from       'lib/Class/C3/XS.pm';
build_requires 'Test::More' => '0.47';
auto_install;
WriteAll;
