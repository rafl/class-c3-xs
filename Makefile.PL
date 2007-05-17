use inc::Module::Install;

name           'Class-C3-XS';
all_from       'lib/Class/C3/XS.pm';
build_requires 'Test::More' => '0.47';

# Rebuild README for maintainers
if(-e 'MANIFEST.SKIP') {
    system("pod2text lib/Class/C3/XS.pm >README");
}

auto_install;
WriteAll;
