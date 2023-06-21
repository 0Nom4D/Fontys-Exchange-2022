import 'package:flutter/material.dart';

const Color primaryColor = Color(0xFF50C878);

const Color secondaryColor = Color(0xFFFFFFD4);

const Color successColor = Color(0xFF00B74A);

const Color dangerColor = Color(0xFFF93154);

const Color warningColor = Color(0xFFFFA900);

const Color infoColor = Color(0xFF39C0ED);

const ColorScheme appScheme = ColorScheme(
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

class AppTheme {
  static final ThemeData defaultTheme = ThemeData.from(colorScheme: appScheme);
}
