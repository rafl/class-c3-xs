
package Class::C3::XS;

our $VERSION = '0.15';

=pod

=head1 NAME

Class::C3::XS - The XS implementation of Class::C3

=head1 DESCRIPTION

This is the XS implementation of L<Class::C3>.  The main L<Class::C3> package will
first attempt to load L<Class::C3::XS>, and then failing that, will fall back to 
L<Class::C3::PurePerl>.  Do not use this package directly, use L<Class::C3> instead.

=head1 AUTHOR

Stevan Little, E<lt>stevan@iinteractive.comE<gt>

Brandon L. Black, E<lt>blblack@gmail.comE<gt>

=head1 COPYRIGHT AND LICENSE

Copyright 2005, 2006 by Infinity Interactive, Inc.

L<http://www.iinteractive.com>

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself. 

=cut

package # hide me from PAUSE
    Class::C3;

use strict;
use warnings;

use Scalar::Util 'blessed';
use Algorithm::C3;

# this is our global stash of both 
# MRO's and method dispatch tables
# the structure basically looks like
# this:
#
#   $MRO{$class} = {
#      MRO => [ <class precendence list> ],
#      methods => {
#          orig => <original location of method>,
#          code => \&<ref to original method>
#      },
#      has_overload_fallback => (1 | 0)
#   }
#
our %MRO;

# use these for debugging ...
sub _dump_MRO_table { %MRO }
our $TURN_OFF_C3 = 0;

# state tracking for initialize()/uninitialize()
our $_initialized = 0;

sub import {
    my $class = caller();
    # skip if the caller is main::
    # since that is clearly not relevant
    return if $class eq 'main';
    return if $TURN_OFF_C3;
    # make a note to calculate $class 
    # during INIT phase
    $MRO{$class} = undef unless exists $MRO{$class};
}

## initializers

sub initialize {
    # why bother if we don't have anything ...
    return unless keys %MRO;
    if($_initialized) {
        uninitialize();
        $MRO{$_} = undef foreach keys %MRO;
    }
    _calculate_method_dispatch_tables();
    _apply_method_dispatch_tables();
    %next::METHOD_CACHE = ();
    $_initialized = 1;
}

sub uninitialize {
    # why bother if we don't have anything ...
    return unless keys %MRO;    
    _remove_method_dispatch_tables();    
    %next::METHOD_CACHE = ();
    $_initialized = 0;
}

sub reinitialize { goto &initialize }

## functions for applying C3 to classes

sub _calculate_method_dispatch_tables {
    my %merge_cache;
    foreach my $class (keys %MRO) {
        _calculate_method_dispatch_table($class, \%merge_cache);
    }
}

sub _calculate_method_dispatch_table {
    my ($class, $merge_cache) = @_;
    no strict 'refs';
    my @MRO = calculateMRO($class, $merge_cache);
    $MRO{$class} = { MRO => \@MRO };
    my $has_overload_fallback = 0;
    my %methods;
    # NOTE: 
    # we do @MRO[1 .. $#MRO] here because it
    # makes no sense to interogate the class
    # which you are calculating for. 
    foreach my $local (@MRO[1 .. $#MRO]) {
        # if overload has tagged this module to 
        # have use "fallback", then we want to
        # grab that value 
        $has_overload_fallback = ${"${local}::()"} 
            if defined ${"${local}::()"};
        foreach my $method (grep { defined &{"${local}::$_"} } keys %{"${local}::"}) {
            # skip if already overriden in local class
            next unless !defined *{"${class}::$method"}{CODE};
            $methods{$method} = {
                orig => "${local}::$method",
                code => \&{"${local}::$method"}
            } unless exists $methods{$method};
        }
    }    
    # now stash them in our %MRO table
    $MRO{$class}->{methods} = \%methods; 
    $MRO{$class}->{has_overload_fallback} = $has_overload_fallback;        
}

sub _apply_method_dispatch_tables {
    foreach my $class (keys %MRO) {
        _apply_method_dispatch_table($class);
    }     
}

sub _apply_method_dispatch_table {
    my $class = shift;
    no strict 'refs';
    ${"${class}::()"} = $MRO{$class}->{has_overload_fallback}
        if $MRO{$class}->{has_overload_fallback};
    foreach my $method (keys %{$MRO{$class}->{methods}}) {
        *{"${class}::$method"} = $MRO{$class}->{methods}->{$method}->{code};
    }    
}

sub _remove_method_dispatch_tables {
    foreach my $class (keys %MRO) {
        _remove_method_dispatch_table($class);
    }       
}

sub _remove_method_dispatch_table {
    my $class = shift;
    no strict 'refs';
    delete ${"${class}::"}{"()"} if $MRO{$class}->{has_overload_fallback};    
    foreach my $method (keys %{$MRO{$class}->{methods}}) {
        delete ${"${class}::"}{$method}
            if defined *{"${class}::${method}"}{CODE} && 
               (*{"${class}::${method}"}{CODE} eq $MRO{$class}->{methods}->{$method}->{code});       
    }   
}

## functions for calculating C3 MRO

sub calculateMRO {
    my ($class, $merge_cache) = @_;
    return Algorithm::C3::merge($class, sub { 
        no strict 'refs'; 
        @{$_[0] . '::ISA'};
    }, $merge_cache);
}

package  # hide me from PAUSE
    next; 

use strict;
use warnings;

our $VERSION = 0.15;

use Scalar::Util 'blessed';

our %METHOD_CACHE;

sub method {
    my $indirect = caller() =~ /^(?:next|maybe::next)$/;
    my $level = $indirect ? 2 : 1;
     
    my ($method_caller, $label, @label);
    while ($method_caller = (caller($level++))[3]) {
      @label = (split '::', $method_caller);
      $label = pop @label;
      last unless
        $label eq '(eval)' ||
        $label eq '__ANON__';
    }
    my $caller   = join '::' => @label;    
    my $self     = $_[0];
    my $class    = blessed($self) || $self;
    
    my $method = $METHOD_CACHE{"$class|$caller|$label"} ||= do {
        
        my @MRO = Class::C3::calculateMRO($class);
        
        my $current;
        while ($current = shift @MRO) {
            last if $caller eq $current;
        }
        
        no strict 'refs';
        my $found;
        foreach my $class (@MRO) {
            next if (defined $Class::C3::MRO{$class} && 
                     defined $Class::C3::MRO{$class}{methods}{$label});          
            last if (defined ($found = *{$class . '::' . $label}{CODE}));
        }
        
        $found;
    };

    return $method if $indirect;

    die "No next::method '$label' found for $self" if !$method;

    goto &{$method};
}

sub can { method($_[0]) }

package  # hide me from PAUSE
    maybe::next; 

use strict;
use warnings;

our $VERSION = 0.15;

sub method { (next::method($_[0]) || return)->(@_) }

1;
