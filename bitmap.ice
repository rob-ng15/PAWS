algorithm bitmap(
    simple_dualport_bram_port0 bitmap_0A,
    simple_dualport_bram_port0 bitmap_1A,
    simple_dualport_bram_port0 bitmap_0R,
    simple_dualport_bram_port0 bitmap_1R,
    simple_dualport_bram_port0 bitmap_0G,
    simple_dualport_bram_port0 bitmap_1G,
    simple_dualport_bram_port0 bitmap_0B,
    simple_dualport_bram_port0 bitmap_1B,
    input   uint1   framebuffer,
    input   uint10  pix_x,
    input   uint10  pix_y,
    input   uint1   pix_active,
    input   uint1   pix_vblank,
    output! uint6   pixel,
    output! uint1   bitmap_display,

    // Pixel reader
    input   uint9   bitmap_x_read,
    input   uint9   bitmap_y_read,
    output  uint7   bitmap_colour_read
) <autorun,reginputs> {
    // Pixel x and y fetching 1 in advance due to bram latency
    uint9   x_plus_one <: pix_x[1,9] + pix_x[0,1];                uint8   y_line <: pix_vblank ? 0 : pix_y[1,8];
    uint9   x_pixel <: pix_active ? x_plus_one : 0; uint17  address <: y_line * 320 + x_pixel;

    // Pixel being read?
    bitmap_colour_read := ( pix_x == bitmap_x_read ) & ( pix_y == bitmap_y_read ) ?
                            ( framebuffer ? { bitmap_1A.rdata0, bitmap_1R.rdata0, bitmap_1G.rdata0, bitmap_1B.rdata0 } : { bitmap_0A.rdata0, bitmap_0R.rdata0, bitmap_0G.rdata0, bitmap_0B.rdata0 } )
                            : bitmap_colour_read;

    // Setup the address in the bitmap for the pixel being rendered
    // Use pre-fetching of the next pixel ready for the next cycle
    // y_line * 320 + x_pixel
    bitmap_0A.addr0 := address; bitmap_0R.addr0 := address; bitmap_0G.addr0 := address; bitmap_0B.addr0 := address;
    bitmap_1A.addr0 := address; bitmap_1R.addr0 := address; bitmap_1G.addr0 := address; bitmap_1B.addr0 := address;

    // RENDER - Default to transparent
    bitmap_display := pix_active & ~( framebuffer ? bitmap_1A.rdata0 : bitmap_0A.rdata0 );
    pixel := framebuffer ? { bitmap_1R.rdata0, bitmap_1G.rdata0, bitmap_1B.rdata0 } : { bitmap_0R.rdata0, bitmap_0G.rdata0, bitmap_0B.rdata0 };
}

algorithm bitmapwriter(
    // GPU Parameters
    input   int11   gpu_x,
    input   int11   gpu_y,
    input   uint7   gpu_colour,
    input   uint7   gpu_colour_alt,
    input   int11   gpu_param0,
    input   int11   gpu_param1,
    input   int11   gpu_param2,
    input   int11   gpu_param3,
    input   int11   gpu_param4,
    input   int11   gpu_param5,
    input   uint4   gpu_write,
    input   uint4   gpu_dithermode,

    // CROP RECTANGLE
    input   uint9   crop_left,
    input   uint9   crop_right,
    input   uint8   crop_top,
    input   uint8   crop_bottom,

    // Colours for the pixelblock
    input   uint7   pb_colour7,
    input   uint8   pb_colour8r,
    input   uint8   pb_colour8g,
    input   uint8   pb_colour8b,
    input   uint2   pb_newpixel,

    // VECTOR BLOCK
    input   uint5   vector_block_number,
    input   uint7   vector_block_colour,
    input   int11   vector_block_xc,
    input   int11   vector_block_yc,
    input   uint3   vector_block_scale,
    input   uint3   vector_block_action,
    input   uint1   draw_vector,

    output  uint1   gpu_queue_full,
    output  uint1   gpu_queue_complete,
    output  uint1   vector_block_active,
    input   uint6   static6bit,

    // BITMAP TO WRITE
    input   uint1   framebuffer,
    simple_dualport_bram_port1 bitmap_0A,
    simple_dualport_bram_port1 bitmap_1A,
    simple_dualport_bram_port1 bitmap_0R,
    simple_dualport_bram_port1 bitmap_1R,
    simple_dualport_bram_port1 bitmap_0G,
    simple_dualport_bram_port1 bitmap_1G,
    simple_dualport_bram_port1 bitmap_0B,
    simple_dualport_bram_port1 bitmap_1B,

    simple_dualport_bram_port0 blit1tilemap,
    simple_dualport_bram_port0 characterGenerator8x8,
    simple_dualport_bram_port0 colourblittilemap,
    simple_dualport_bram_port0 vertex
) <autorun,reginputs> {
    // VECTOR DRAWER UNIT
    vectors vector_drawer(
        vector_block_number <: vector_block_number,
        vector_block_xc <: vector_block_xc,
        vector_block_yc <: vector_block_yc,
        vector_block_scale <: vector_block_scale,
        vector_block_action <: vector_block_action,
        draw_vector <: draw_vector,
        vector_block_active :> vector_block_active,
        vertex <:> vertex,
        gpu_active <: QUEUE.gpu_active
    );

    // GPU QUEUE CONTROLLER, WITH OUTPUTS FOR WRITING PIXELS
    gpu_queue QUEUE(
        crop_left <: crop_left,
        crop_right <: crop_right,
        crop_top <: crop_top,
        crop_bottom <: crop_bottom,
        gpu_x <: gpu_x,
        gpu_y <: gpu_y,
        gpu_colour <: gpu_colour,
        gpu_colour_alt <: gpu_colour_alt,
        gpu_param0 <: gpu_param0,
        gpu_param1 <: gpu_param1,
        gpu_param2 <: gpu_param2,
        gpu_param3 <: gpu_param3,
        gpu_param4 <: gpu_param4,
        gpu_param5 <: gpu_param5,
        gpu_write <: gpu_write,
        gpu_dithermode <: gpu_dithermode,
        blit1tilemap <:> blit1tilemap,
        characterGenerator8x8 <:> characterGenerator8x8,
        colourblittilemap <:> colourblittilemap,
        pb_colour7 <: pb_colour7,
        pb_colour8r <: pb_colour8r,
        pb_colour8g <: pb_colour8g,
        pb_colour8b <: pb_colour8b,
        pb_newpixel <: pb_newpixel,
        vector_block_colour <: vector_block_colour,
        vector_drawer_gpu_x <: vector_drawer.gpu_x,
        vector_drawer_gpu_y <: vector_drawer.gpu_y,
        vector_drawer_gpu_param0 <: vector_drawer.gpu_param0,
        vector_drawer_gpu_param1 <: vector_drawer.gpu_param1,
        vector_drawer_gpu_write <: vector_drawer.gpu_write,
        vector_block_active <: vector_block_active,
        queue_full :> gpu_queue_full,
        queue_complete :> gpu_queue_complete
    );

    uint7   pixeltowrite <:: ( QUEUE.gpu_active_dithermode == 14 ) ? static6bit : DODITHER.condition ? QUEUE.bitmap_colour_write : QUEUE.bitmap_colour_write_alt;
    dither DODITHER( bitmap_x_write <: QUEUE.bitmap_x_write, bitmap_y_write <: QUEUE.bitmap_y_write, dithermode <: QUEUE.gpu_active_dithermode, static1bit <: static6bit[0,1] );

    // Write in range?
    uint1   write_pixel <:: ( QUEUE.bitmap_x_write >= QUEUE.bitmap_crop_left ) & (QUEUE. bitmap_x_write <= QUEUE.bitmap_crop_right ) &
                            ( QUEUE.bitmap_y_write >= QUEUE.bitmap_crop_top ) & ( QUEUE.bitmap_y_write <= QUEUE.bitmap_crop_bottom ) & QUEUE.bitmap_write;
    uint1   write_buffer0 <:: write_pixel & ~framebuffer;
    uint1   write_buffer1 <:: write_pixel & framebuffer;

    // LOCK BITMAP ADDRESSES, PIXEL VALUE, AND WRITE FLAGS
    uint17  address <:: QUEUE.bitmap_y_write[0,8] * 320 + QUEUE.bitmap_x_write[0,9];
    bitmap_0A.wenable1 := write_buffer0; bitmap_0R.wenable1 := write_buffer0; bitmap_0G.wenable1 := write_buffer0; bitmap_0B.wenable1 := write_buffer0;
    bitmap_1A.wenable1 := write_buffer1; bitmap_1R.wenable1 := write_buffer1; bitmap_1G.wenable1 := write_buffer1; bitmap_1B.wenable1 := write_buffer1;

    bitmap_1A.addr1 := address; bitmap_1A.wdata1 := pixeltowrite[6,1];                                  bitmap_1R.addr1 := address; bitmap_1R.wdata1 := pixeltowrite[4,2];
    bitmap_1G.addr1 := address; bitmap_1G.wdata1 := pixeltowrite[2,2];                                  bitmap_1B.addr1 := address; bitmap_1B.wdata1 := pixeltowrite[0,2];

    bitmap_0A.addr1 := address; bitmap_0A.wdata1 := pixeltowrite[6,1];                                  bitmap_0R.addr1 := address; bitmap_0R.wdata1 := pixeltowrite[4,2];
    bitmap_0G.addr1 := address; bitmap_0G.wdata1 := pixeltowrite[2,2];                                  bitmap_0B.addr1 := address; bitmap_0B.wdata1 := pixeltowrite[0,2];
}

algorithm dither(
    input   uint9   bitmap_x_write,
    input   uint8   bitmap_y_write,
    input   uint4   dithermode,
    input   uint1   static1bit,
    output! uint1   condition
) <autorun> {
    uint4   checkmode <: dithermode - 1;            uint3   revbitmapx <: 3b111 - bitmap_x_write[0,3];

    always_after {
        // DITHER PATTERNS
        // == 0 SOLID == 1 SMALL CHECKERBOARD == 2 MED CHECKERBOARD == 3 LARGE CHECKERBOARD
        // == 4 VERTICAL STRIPES == 5 HORIZONTAL STRIPES == 6 CROSSHATCH == 7 LEFT SLOPE
        // == 8 RIGHT SLOPE == 9 LEFT TRIANGLE == 10 RIGHT TRIANGLE == 11 X
        // == 12 + == 13 BRICK == 14 COLOUR STATIC == 15 STATIC
        switch( dithermode ) {
            case 0: { condition = 1; }                                                                                          // SOLID
            default: { condition = ( bitmap_x_write[checkmode,1] ^ bitmap_y_write[checkmode,1] ); }                             // CHECKERBOARDS 1 2 AND 3
            case 4: { condition = bitmap_x_write[0,1]; }                                                                        // VERTICAL STRIPES
            case 5: { condition = bitmap_y_write[0,1]; }                                                                        // HORIZONTAL STRIPES
            case 6: { condition = ( bitmap_x_write[0,1] | bitmap_y_write[0,1] ); }                                              // CROSSHATCH
            case 7: { condition = ( bitmap_x_write[0,2] == bitmap_y_write[0,2] ); }                                             // LEFT SLOPE
            case 8: { condition = ( bitmap_x_write[0,2] == ~bitmap_y_write[0,2] ); }                                            // RIGHT SLOPE
            case 9: { condition = ( bitmap_x_write[0,3] <= bitmap_y_write[0,3] ); }                                             // LEFT TRIANGLE
            case 10: { condition = ( revbitmapx <= bitmap_y_write[0,3] ); }                                                     // RIGHT TRIANGLE
            case 11: { condition = ( bitmap_x_write[0,3] == bitmap_y_write[0,3] ) | ( revbitmapx == bitmap_y_write[0,3] ); }    // X
            case 12: { condition = ( bitmap_x_write[1,2] == 2b10 ) | ( bitmap_y_write[1,2] == 2b10 ); }                         // +
            case 13: { condition = ( ~|bitmap_y_write[0,2] ) | ( bitmap_x_write[0,2] == { bitmap_y_write[2,1], 1b0 } ); }       // BRICK
            case 14: {}                                                                                                         // COLOUR STATIC (placeholder, done in main)
            case 15: { condition = static1bit; }                                                                                // STATIC
        }
    }
}
