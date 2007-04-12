
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

/* TODO: put __calculate_mro here, from blead patch's mro_linear_c3 */
/* TODO: put __nextcan / __poptosubat here, from blead patch */

MODULE = Class::C3::XS  PACKAGE = Class::C3::XS

/* TODO: put calculateMRO here, uses __calculate_mro */
 
MODULE = Class::C3::XS	PACKAGE = next

/* TODO: put next::method / next::can here */

MODULE = Class::C3::XS	PACKAGE = maybe

/* TODO: put maybe::next::method here */
