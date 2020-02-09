$(function () {
    $('.sub-menu').on({
        'mouseenter': function () {
            $(this).addClass('is-active');
        },
        'mouseleave': function () {
            $(this).removeClass('is-active');
        }
    });


    $('#nav-toggle,#overlay').on('click', function() {
        $('body').toggleClass('open');
    });
});