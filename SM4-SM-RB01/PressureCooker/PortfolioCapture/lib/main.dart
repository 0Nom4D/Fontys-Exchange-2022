import 'package:flutter/material.dart';
import 'package:flutter_secure_storage/flutter_secure_storage.dart';
import 'package:get_it/get_it.dart';
import 'package:portfolio_capture/providers/portfolio_provider.dart';

import 'package:portfolio_capture/src/portfolio_startup.dart';
import 'package:provider/provider.dart';

import 'package:flutter_screenutil/flutter_screenutil.dart';

import 'package:timeago_flutter/timeago_flutter.dart' as timeago;
import 'package:portfolio_capture/theme.dart';

void initTimeago() {
  timeago.setLocaleMessages('en', EnTimeagoMessage());
  timeago.setLocaleMessages('en_short', EnTimeagoShortMessage());
}

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  GetIt.I.registerSingleton<FlutterSecureStorage>(const FlutterSecureStorage());

  initTimeago();
  runApp(
    MultiProvider(
      providers: [
        ChangeNotifierProvider(create: (_) => PortfolioProvider()),
      ],
      child: const PortfolioCaptureApp()
    )
  );
}

class PortfolioCaptureApp extends StatelessWidget {
  static GlobalKey<NavigatorState> gKey = GlobalKey<NavigatorState>();

  const PortfolioCaptureApp({super.key});

  @override
  Widget build(BuildContext context) =>
    ScreenUtilInit(
      minTextAdapt: true,
      splitScreenMode: true,
      builder: (context, child) =>
        MaterialApp(
          theme: PortfolioAppTheme.defaultTheme,
          debugShowCheckedModeBanner: false,
          title: "PortfolioCapture",
          initialRoute: PortfolioStartup.routeName,
          routes: {
            PortfolioStartup.routeName: (context) => const PortfolioStartup(),
          },
          builder: (context, widget) {
            ScreenUtil.init(context);
            return MediaQuery(
              data: MediaQuery.of(context).copyWith(
                textScaleFactor: 1.0
              ),
              child: widget!,
            );
          },
          navigatorKey: gKey,
        ),
    );
}
