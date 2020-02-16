$(function () {
    $('.sub-menu').on({
        'mouseenter': function () {
            $(this).addClass('is-active');
        },
        'mouseleave': function () {
            $(this).removeClass('is-active');
        }
    });
    $('.sub-sub-menu').on({
        'mouseenter': function () {
            $(this).addClass('is-active');
        },
        'mouseleave': function () {
            $(this).removeClass('is-active');
        }
    });

    $('.sub-sub-menu').on('transitionend', function() {
        if('sub-menu')
    });

    $('#nav-toggle,#overlay').on('click', function() {
        $('body').toggleClass('open');
    });
});