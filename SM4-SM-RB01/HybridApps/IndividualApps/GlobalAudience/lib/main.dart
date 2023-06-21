// coverage:ignore-file

import 'package:flutter_localizations/flutter_localizations.dart';
import 'package:flutter_gen/gen_l10n/app_localizations.dart';
import 'package:devicelocale/devicelocale.dart';

import 'package:provider/provider.dart';
import 'package:flutter/material.dart';

import 'package:global_audience/src/providers/locale_provider.dart';
import 'package:global_audience/src/home_page.dart';
import 'package:global_audience/src/theme.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  runApp(
    MultiProvider(
      providers: [ChangeNotifierProvider(create: (_) => LocaleProvider())],
      child: const MyApp(),
    )
  );
}

class MyApp extends StatefulWidget {
  const MyApp({super.key});

  @override
  MyAppState createState() => MyAppState();
}

class MyAppState extends State<MyApp> with WidgetsBindingObserver {
  @override
  void initState() {
    super.initState();

    WidgetsBinding.instance.addObserver(this);

    LocaleProvider localeProvider = Provider.of<LocaleProvider>(context, listen: false);
    Devicelocale.currentLocale.then((data) {
      localeProvider.updateLocale(data!.substring(0, 2).toLowerCase());
    });
  }

  @override
  void didChangeLocales(List<Locale>? locales) {
    LocaleProvider localeProvider = Provider.of<LocaleProvider>(context, listen: false);

    Devicelocale.currentLocale.then((data) {
      localeProvider.updateLocale(data!.substring(0, 2).toLowerCase());
    });
  }

  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      title: "Arthur's TV Reviews",
      debugShowCheckedModeBanner: false,
      localizationsDelegates: const [
        AppLocalizations.delegate,
        GlobalMaterialLocalizations.delegate,
        GlobalWidgetsLocalizations.delegate,
        GlobalCupertinoLocalizations.delegate,
      ],
      supportedLocales: const [
        Locale('ar'),
        Locale('da'),
        Locale('de'),
        Locale('en'),
        Locale('es'),
        Locale('fr'),
        Locale('it'),
        Locale('nl'),
        Locale('pt'),
      ],
      locale: context.watch<LocaleProvider>().appLocale,
      theme: AppTheme.defaultTheme,
      home: const MainPage()
    );
  }
}
