import 'package:flutter/material.dart';

import 'package:camera/camera.dart';
import 'package:go_router/go_router.dart';

import 'package:psv_fan_experience/src/views/submission_screen.dart';
import 'package:psv_fan_experience/src/widgets/bottom_navbar.dart';
import 'package:psv_fan_experience/src/views/camera_screen.dart';
import 'package:psv_fan_experience/src/views/upload_screen.dart';
import 'package:psv_fan_experience/src/views/competitons.dart';
import 'package:psv_fan_experience/src/views/profile.dart';
import 'package:psv_fan_experience/src/models/user.dart';

final _mainNavigationKey = GlobalKey<NavigatorState>();
final _shellNavigationKey = GlobalKey<NavigatorState>();

final router = GoRouter(
  initialLocation: '/',
  navigatorKey: _mainNavigationKey,
  routes: [
    ShellRoute(
      navigatorKey: _shellNavigationKey,
      builder: (context, state, child) => ScaffoldWithBottomNavBar(child: child),
      routes: [
        GoRoute(
          path: "/",
          pageBuilder: (context, state) => const NoTransitionPage(
            child: SubmissionScreen()
          ),
          routes: [
            GoRoute(
              path: "profile",
              pageBuilder: (context, state) => NoTransitionPage(
                child: ProfilePage(user: User.placeholderUser)
              ),
              routes: const []
            ),
          ]
        ),
        GoRoute(
          path: "/camera",
          pageBuilder: (context, state) => const NoTransitionPage(
            child: CameraPage()
          ),
          routes: [
            GoRoute(
              path: "upload",
              pageBuilder: (context, state) => NoTransitionPage(
                child: SubmissionUploadPage(state.extra as XFile),
              ),
              routes: const []
            ),
            GoRoute(
              path: "profile",
              pageBuilder: (context, state) => NoTransitionPage(
                child: ProfilePage(user: User.placeholderUser)
              ),
              routes: const []
            )
          ]
        ),
        GoRoute(
          path: "/competitions",
          pageBuilder: (context, state) => NoTransitionPage(
            child: CompetitionsPage()
          ),
          routes: [
            GoRoute(
              path: ":competitionId",
              pageBuilder: (context, state) => NoTransitionPage(
                child: SubmissionScreen(selectedCompetition: state.pathParameters['competitionId']!)
              ),
              routes: [
                GoRoute(
                  path: "profile",
                  pageBuilder: (context, state) => NoTransitionPage(
                    child: ProfilePage(user: User.placeholderUser)
                  ),
                  routes: const []
                )
              ]
            ),
            GoRoute(
              path: "profile",
              pageBuilder: (context, state) => NoTransitionPage(
                child: ProfilePage(user: User.placeholderUser)
              ),
              routes: const []
            ),
          ]
        ),
      ]
    )
  ]
);