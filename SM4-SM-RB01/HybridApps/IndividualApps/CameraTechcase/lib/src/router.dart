import 'dart:typed_data';
import 'package:flutter/material.dart';

import 'package:camera/camera.dart';
import 'package:go_router/go_router.dart';
import 'package:photo_manager/photo_manager.dart';

import 'package:camera_techcase/src/views/video_player_screen.dart';
import 'package:camera_techcase/src/views/image_viewer_screen.dart';
import 'package:camera_techcase/src/widgets/bottom_navbar.dart';
import 'package:camera_techcase/src/views/confirm_screen.dart';
import 'package:camera_techcase/src/views/gallery_screen.dart';
import 'package:camera_techcase/src/views/camera_screen.dart';

final _mainNavigationKey = GlobalKey<NavigatorState>();
final _shellNavigationKey = GlobalKey<NavigatorState>();

final router = GoRouter(
    initialLocation: '/camera',
    navigatorKey: _mainNavigationKey,
    routes: [
      ShellRoute(
        navigatorKey: _shellNavigationKey,
        builder: (context, state, child) => ScaffoldWithBottomNavBar(child: child),
        routes: [
          GoRoute(
            path: "/camera",
            pageBuilder: (context, state) => const NoTransitionPage(
              child: CameraPage()
            ),
            routes: [
              GoRoute(
                path: "save",
                pageBuilder: (context, state) => NoTransitionPage(
                  child: ConfirmScreen(state.extra as XFile)
                ),
                routes: const []
              ),
            ]
          ),
          GoRoute(
            path: "/gallery",
            pageBuilder: (context, state) => const NoTransitionPage(
              child: GridGallery()
            ),
            routes: [
              GoRoute(
                path: ":imageName",
                pageBuilder: (context, state) {
                  Uint8List imageData = state.extra as Uint8List;

                  return NoTransitionPage(
                    child: ImageViewerScreen(title: state.pathParameters['imageName']!, imageData: imageData)
                  );
                },
                routes: const []
              ),
              GoRoute(
                path: "video/:videoId",
                pageBuilder: (context, state) {
                  AssetEntity videoEntity = state.extra as AssetEntity;

                  return NoTransitionPage(
                    child: VideoViewerScreen(title: state.pathParameters['videoId']!, videoEntity: videoEntity)
                  );
                },
                routes: const []
              ),
            ]
          ),
        ]
      )
    ]
);