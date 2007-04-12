
package Class::C3::XS;

our $VERSION = '0.15';

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

Stevan Little, E<lt>stevan@iinteractive.comE<gt>

Brandon L. Black, E<lt>blblack@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright 2005, 2006 by Infinity Interactive, Inc.

L<http://www.iinteractive.com>

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself. 

=cut

# TODO: put XSLoader stuff here
# TODO: shut off redef warnings and set Class::C3::calculateMRO = Class::C3::XS::calculateMRO

1;
