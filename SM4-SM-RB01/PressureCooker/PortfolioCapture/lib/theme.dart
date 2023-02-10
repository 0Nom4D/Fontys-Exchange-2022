// coverage:ignore-file
import 'package:flutter/material.dart';
import 'package:timeago_flutter/timeago_flutter.dart';

// Changed colors because it was too hard to put logo with.
const Color primaryColor = Color(0xFFFE7C01);

const Color secondaryColor = Color(0xFF011EF4);

const Color successColor = Color(0xFF00B74A);

const Color dangerColor = Color(0xFFF93154);

const Color warningColor = Color(0xFFFFA900);

const Color infoColor = Color(0xFF39C0ED);

const ColorScheme portfolioTheme = ColorScheme(
    primary: primaryColor,
    secondary: secondaryColor,
    background: Colors.white,
    brightness: Brightness.light,
    onError: dangerColor,
    error: dangerColor,
    onPrimary: Colors.white,
    onSecondary: primaryColor,
    onBackground: primaryColor,
    surface: Colors.white,
    onSurface: Colors.grey
);

class PortfolioAppTheme {
  static final ThemeData defaultTheme = ThemeData.from(colorScheme: portfolioTheme);
}

class EnTimeagoMessage extends EnMessages {
  @override
  String lessThanOneMinute(int seconds) => '$seconds seconds';
  @override
  String aboutAMinute(int minutes) => '1 minute';
  @override
  String minutes(int minutes) => '$minutes minutes';
  @override
  String aboutAnHour(int minutes) => '1 hour';
  @override
  String hours(int hours) => '$hours hours';
  @override
  String aDay(int hours) => '1 day';
  @override
  String days(int days) => '$days days';
  @override
  String aboutAMonth(int days) => '1 month';
  @override
  String months(int months) => '$months months';
  @override
  String aboutAYear(int year) => '1 year';
  @override
  String years(int years) => '$years years';
}

class EnTimeagoShortMessage extends EnShortMessages {
  @override
  String suffixAgo() => 'ago';
  @override
  String suffixFromNow() => 'from now';
  @override
  String lessThanOneMinute(int seconds) => '${seconds}s';
  @override
  String aboutAMinute(int minutes) => '1m';
  @override
  String minutes(int minutes) => '${minutes}m';
  @override
  String aboutAnHour(int minutes) => '1h';
  @override
  String hours(int hours) => '${hours}h';
  @override
  String aDay(int hours) => '1d';
  @override
  String days(int days) => '${days}d';
  @override
  String aboutAMonth(int days) => '1mo';
  @override
  String months(int months) => '${months}mo';
  @override
  String aboutAYear(int year) => '1y';
  @override
  String years(int years) => '${years}y';
}
