package Class::C3::XS;

our $VERSION = '0.01_06';

=pod

=head1 NAME

Class::C3::XS - XS speedups for Class::C3

=head1 SUMMARY

  use Class::C3; # Automatically loads Class::C3::XS
                 #  if it's installed locally

=head1 DESCRIPTION

This contains XS performance enhancers for L<Class::C3>.
The main L<Class::C3> package will use this package automatically
if it can find it.  Do not use this package directly, use
L<Class::C3> instead.

=head1 AUTHOR

Brandon L. Black, E<lt>blblack@gmail.comE<gt>

=head1 LICENSE

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself. 

=cut

require XSLoader;
XSLoader::load('Class::C3::XS', $VERSION);

1;
