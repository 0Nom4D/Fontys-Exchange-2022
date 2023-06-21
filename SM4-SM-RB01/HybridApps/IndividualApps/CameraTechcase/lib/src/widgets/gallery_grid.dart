import 'dart:typed_data';

import 'package:flutter/material.dart';

import 'package:photo_manager/photo_manager.dart';
import 'package:go_router/go_router.dart';

class GalleryGrid extends StatefulWidget {
  const GalleryGrid({super.key});

  @override
  State<GalleryGrid> createState() => _GalleryGridState();
}

class _GalleryGridState extends State<GalleryGrid> {
  ScrollController scrollController = ScrollController();
  final List<Widget> _mediaList = [];
  int currentPage = 0;
  int? lastPage;

  @override
  void initState() {
    super.initState();
    _fetchNewMedia();
  }

  _handleScrollEvent(ScrollNotification scroll) {
    if (scroll.metrics.pixels / scroll.metrics.maxScrollExtent > 0.33) {
      if (currentPage != lastPage) {
        _fetchNewMedia();
      }
    }
  }

  _fetchNewMedia() async {
    lastPage = currentPage;
    final PermissionState ps = await PhotoManager.requestPermissionExtend();
    if (ps.isAuth) {
      List<AssetPathEntity> albums = await PhotoManager.getAssetPathList(onlyAll: true);
      List<AssetEntity> media = await albums[0].getAssetListPaged(size: 60, page: currentPage);
      List<Widget> temp = [];
      for (var asset in media) {
        temp.add(
          FutureBuilder(
            future: asset.thumbnailDataWithSize(const ThumbnailSize(200, 200)),
            builder: (BuildContext context, AsyncSnapshot<Uint8List?> snapshot) {
              if (snapshot.connectionState == ConnectionState.done) {
                return InkWell(
                  onTap: asset.type == AssetType.image ? () {
                    GoRouter.of(context).go('/gallery/${asset.id}', extra: snapshot.data!);
                  } : () {
                    GoRouter.of(context).go('/gallery/video/${asset.id}', extra: asset);
                  },
                  child: Stack(
                    children: <Widget>[
                      Positioned.fill(
                        child: Image.memory(
                          snapshot.data!,
                          fit: BoxFit.cover,
                        ),
                      ),
                      if (asset.type == AssetType.video)
                        const Align(
                          alignment: Alignment.bottomRight,
                          child: Padding(
                            padding: EdgeInsets.only(right: 5, bottom: 5),
                            child: Icon(
                              Icons.videocam,
                              color: Colors.white,
                            ),
                          ),
                        ),
                    ],
                  ),
                );
              }
              return Container();
            },
          ),
        );
      }
      setState(() {
        _mediaList.addAll(temp);
        currentPage++;
      });
    }
  }

  @override
  Widget build(BuildContext context) {
    return NotificationListener<ScrollNotification>(
      onNotification: (ScrollNotification scroll) {
        _handleScrollEvent(scroll);
        return false;
      },
      child: GridView.builder(
        controller: scrollController,
        itemCount: _mediaList.length,
        gridDelegate: const SliverGridDelegateWithFixedCrossAxisCount(crossAxisCount: 3),
        itemBuilder: (BuildContext context, int index) {
          return _mediaList[index];
        }
      )
    );
  }
}