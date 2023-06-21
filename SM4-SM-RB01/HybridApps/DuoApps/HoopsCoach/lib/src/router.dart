import 'package:app/src/views/image_analysis_result.dart';
import 'package:app/src/views/video_analysis_result.dart';
import 'package:flutter/cupertino.dart';
import 'package:go_router/go_router.dart';

import 'package:app/src/widgets/bottom_navbar.dart';

import 'package:app/src/views/exercise_details.dart';
import 'package:app/src/views/exercises_view.dart';
import 'package:app/src/views/progress_view.dart';
import 'package:app/src/views/profile_view.dart';
import 'package:app/src/views/home_view.dart';

final _rootNavigatorKey = GlobalKey<NavigatorState>();
final _shellRouteNavigationKey = GlobalKey<NavigatorState>();

final router = GoRouter(
    initialLocation: "/",
    navigatorKey: _rootNavigatorKey,
    routes: [
      ShellRoute(
          navigatorKey: _shellRouteNavigationKey,
          builder: (context, state, child) => ScaffoldWithBottomNavBar(child: child),
          routes: [
            GoRoute(
              path: "/",
              pageBuilder: (context, state) => const NoTransitionPage(
                child: HomeView()
              ),
              routes: [
                GoRoute(
                  path: "exercises/shooting",
                  pageBuilder: (context, state) => const NoTransitionPage(
                    child: ExerciseView()
                  ),
                  routes: [
                    GoRoute(
                      path: "free_throws",
                      pageBuilder: (context, state) => const NoTransitionPage(
                        child: ExerciseDetails()
                      ),
                      routes: [
                        GoRoute(
                          path: "analysis/shoot",
                          pageBuilder: (context, state) => const NoTransitionPage(
                            child: VideoAnalysisResult()
                          ),
                        ),
                        GoRoute(
                          path: "analysis/posture",
                          pageBuilder: (context, state) => const NoTransitionPage(
                            child: ImageAnalysisResult()
                          ),
                        )
                      ]
                    )
                  ]
                )
              ]
            ),
            GoRoute(
              path: "/progress",
              pageBuilder: (context, state) => const NoTransitionPage(
                child: ProgressView()
              ),
            ),
            GoRoute(
              path: "/profile",
              pageBuilder: (context, state) => const NoTransitionPage(
                child: ProfileView()
              ),
            ),
          ]
      )
      // BasePage.routeName: (context) => const BasePage(),
    ]
);
